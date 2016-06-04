//===--- TokenLexer.cpp - Lex from a token stream -------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the TokenLexer interface.
//
//===----------------------------------------------------------------------===//

#include "clang/Lex/TokenLexer.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/LexDiagnostic.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Lex/MacroInfo.h"
#include "clang/Lex/Preprocessor.h"
using namespace clang;

#define DEBUG_PRINTS
#define WITH_LOCATIONS false

#define DUMP_LOCATION(X) llvm::errs() << #X" = ";\
                          X.dump(SM);\
                          llvm::errs() << "\n";\
                          llvm::errs() << "raw = " << X.getRawEncoding() << "\n";\
                          llvm::errs() << "\n";

#define TOK_PARAM isUnexpandableArg
//#define TOK_PARAM isUnexpandableArg
template <class T>
void DUMP_TOKEN_PTR(T tok, const char * end=" ") {
  if (tok->isAnyIdentifier())
    llvm::errs() << tok->getIdentifierInfo()->getName() << "[" << tok->TOK_PARAM << "]";
  else
    llvm::errs() << tok->getName() << "[" << tok->TOK_PARAM << "]";
  llvm::errs() << end;
}

namespace {
#ifdef DEBUG_PRINTS
  std::list<Token> MACRO_STACK;
#endif
  inline int getArgNum(const Token &tok, const MacroInfo *holder) {
    IdentifierInfo *II = tok.getIdentifierInfo();
    return II ? holder->getArgumentNum(II) : -1;
  }

  inline bool tokenForbidsEpansion(const Token &tok) {
    return tok.isOneOf(tok::hashhash, tok::hash);
  }

  inline bool isMacroName(const Token &tok, const Preprocessor &PP) {
    IdentifierInfo *II = tok.getIdentifierInfo();
    if (!II) return false;
    const MacroInfo *m = PP.getMacroInfo(II);
    if (!m) return false;
    return m->isEnabled();
  }

  inline bool isObjectMacroName(const Token &tok, const Preprocessor &PP) {
    IdentifierInfo *II = tok.getIdentifierInfo();
    if (!II) return false;
    const MacroInfo *m = PP.getMacroInfo(II);
    if (!m) return false;
    return m->isObjectLike() && m->isEnabled();
  }

  bool canExpandSomething(const Token* tokens, size_t tokNum, const Preprocessor &PP) {
    for (size_t i = 0; i < tokNum; i++) {
      const Token & CurTok = tokens[i];

      if (CurTok.is(tok::hashhash))
        return true;

      if (isObjectMacroName(CurTok, PP))
        return true;

      if (isMacroName(CurTok, PP) && i + 1 != tokNum && tokens[i+1].is(tok::l_paren))
        return true;
    }
    return false;
  }
}

template<class T>
void validateToks(T toks, size_t sz) {
  int balance = 0;
  for (int i = 0; i < sz; i++) {
    if (toks[i].is(tok::l_guard)) {
      balance++;
    } else if (toks[i].is(tok::r_guard)) {
      balance--;
    }

    assert(balance >= 0);
  }

  assert(balance == 0);
}

/// Create a TokenLexer for the specified macro with the specified actual
/// arguments.  Note that this ctor takes ownership of the ActualArgs pointer.
void TokenLexer::Init(Token &Tok, SourceLocation ELEnd, MacroInfo *MI,
                      MacroArgs *Actuals) {
  // If the client is reusing a TokenLexer, make sure to free any memory
  // associated with it.
  destroy();
#ifdef DEBUG_PRINTS
  if (MI) {
    MACRO_STACK.push_back(Tok);
    llvm::errs() << "expanding macro: "; 
    DUMP_TOKEN_PTR(&Tok, "\n");
  }
#endif
  if (MI) {
    MI->incExpandedTimes();
    //llvm::errs() << "start with MI != 0: " << reinterpret_cast<long long>(this) << "\n";
  }
  //else 
  //  llvm::errs() << "start with MI = 0: " << reinterpret_cast<long long>(this) << "\n";
  Macro = MI;
  ActualArgs = Actuals;
  CurToken = 0;
  ExpandLocStart = Tok.getLocation();
  ExpandLocEnd = ELEnd;
  AtStartOfLine = Tok.isAtStartOfLine();
  HasLeadingSpace = Tok.hasLeadingSpace();
  NextTokGetsSpace = false;
  Tokens = &*Macro->tokens_begin();
  OwnsTokens = false;
  DisableMacroExpansion = false;
  NumTokens = Macro->tokens_end()-Macro->tokens_begin();
  MacroExpansionStart = SourceLocation();
  ReadingFromExpansionCache = false;
  TokensFromCache.clear();
  lexingMode = NORMAL;

  validateToks(Tokens, NumTokens);
  //llvm::errs() << "Enter token: ";
  //DUMP_TOKEN_PTR(&Tok, "\n");
  SourceManager &SM = PP.getSourceManager();
  MacroStartSLocOffset = SM.getNextLocalOffset();

  // let's consider simplest case
  ReadingFromExpansionCache = Macro->isExpansionCacheValid();
  if (ReadingFromExpansionCache) {
    if (!Macro->allNonMacroIIsAreValid(PP)) {
      ReadingFromExpansionCache = false;
      Macro->setExpansionCacheValid(false);
    } else {
      Tokens = &*Macro->exp_tokens_begin();
      NumTokens = Macro->getExpansionCache().size();

     /* llvm::errs() << "Reading from cache:\n";
       for (int i = 0; i < NumTokens; i++) {
         DUMP_TOKEN_PTR(Tokens + i);
       }

       llvm::errs() << "\n";*/
    }
  }

  /*for (int i = 0; i < NumTokens; i++) {
    DUMP_TOKEN_PTR(Tokens + i);
  }
  llvm::errs() << "\n";*/


  if (NumTokens > 0) {
   // llvm::errs() << "Tokens[0] = ";
    //DUMP_TOKEN_PTR(Tokens, "\n");
    assert(Tokens[0].getLocation().isValid());
   // assert((Tokens[0].getLocation().isFileID() || Tokens[0].is(tok::comment)) &&
   //        "Macro defined in macro?");
    assert(ExpandLocStart.isValid());

    // Reserve a source location entry chunk for the length of the macro
    // definition. Tokens that get lexed directly from the definition will
    // have their locations pointing inside this chunk. This is to avoid
    // creating separate source location entries for each token.
    MacroDefStart = SM.getExpansionLoc(Macro->tokens_begin()->getLocation());
    MacroDefLength = Macro->getDefinitionLength(SM);
    MacroExpansionStart = SM.createExpansionLoc(MacroDefStart,
                                                ExpandLocStart,
                                                ExpandLocEnd,
                                                MacroDefLength);
  }

  // If this is a function-like macro, expand the arguments and change
  // Tokens to point to the expanded tokens.
  if (Macro->isFunctionLike() && Macro->getNumArgs()) {
      ExpandFunctionArguments();
  }


  // Mark the macro as currently disabled, so that it is not recursively
  // expanded.  The macro must be disabled only after argument pre-expansion of
  // function-like macro arguments occurs.
  Macro->DisableMacro();
}



/// Create a TokenLexer for the specified token stream.  This does not
/// take ownership of the specified token vector.
void TokenLexer::Init(const Token *TokArray, unsigned NumToks,
                      bool disableMacroExpansion, bool ownsTokens) {
  // If the client is reusing a TokenLexer, make sure to free any memory
  // associated with it.
  destroy();
  if (NumToks) {
    llvm::errs() << "Init of stream with following start: ";
    DUMP_TOKEN_PTR(TokArray, "\n");
  }
  //llvm::errs() << "start without MI: " << reinterpret_cast<long long>(this) << "\n";
  Macro = nullptr;
  ActualArgs = nullptr;
  Tokens = TokArray;
  OwnsTokens = ownsTokens;
  DisableMacroExpansion = disableMacroExpansion;
  NumTokens = NumToks;
  validateToks(Tokens, NumTokens);
  CurToken = 0;
  ExpandLocStart = ExpandLocEnd = SourceLocation();
  AtStartOfLine = false;
  HasLeadingSpace = false;
  NextTokGetsSpace = false;
  MacroExpansionStart = SourceLocation();
  ReadingFromExpansionCache = false;
  lexingMode = NORMAL;
  // Set HasLeadingSpace/AtStartOfLine so that the first token will be
  // returned unmodified.
  if (NumToks != 0) {
    AtStartOfLine   = TokArray[0].isAtStartOfLine();
    HasLeadingSpace = TokArray[0].hasLeadingSpace();
  }
}


void TokenLexer::destroy() {
  // If this was a function-like macro that actually uses its arguments, delete
  // the expanded tokens.
  if (OwnsTokens) {
    delete [] Tokens;
    Tokens = nullptr;
    OwnsTokens = false;
  }

  // TokenLexer owns its formal arguments.
  if (ActualArgs) ActualArgs->destroy(PP);
}

bool TokenLexer::MaybeRemoveCommaBeforeVaArgs(
    SmallVectorImpl<Token> &ResultToks, bool HasPasteOperator, MacroInfo *Macro,
    unsigned MacroArgNo, Preprocessor &PP) {

#ifdef DEBUG_PRINTS
  for (int i = 0; i < NumTokens; i++){
    DUMP_TOKEN_PTR(Tokens + i);
  }
  llvm::errs() << "\n\n";
#endif

  // Is the macro argument __VA_ARGS__?
  if (!Macro->isVariadic() || MacroArgNo != Macro->getNumArgs()-1)
    return false;

  // In Microsoft-compatibility mode, a comma is removed in the expansion
  // of " ... , __VA_ARGS__ " if __VA_ARGS__ is empty.  This extension is
  // not supported by gcc.
  if (!HasPasteOperator && !PP.getLangOpts().MSVCCompat)
    return false;

  // GCC removes the comma in the expansion of " ... , ## __VA_ARGS__ " if
  // __VA_ARGS__ is empty, but not in strict C99 mode where there are no
  // named arguments, where it remains.  In all other modes, including C99
  // with GNU extensions, it is removed regardless of named arguments.
  // Microsoft also appears to support this extension, unofficially.
  if (PP.getLangOpts().C99 && !PP.getLangOpts().GNUMode
        && Macro->getNumArgs() < 2)
    return false;

  // Is a comma available to be removed?
  if (ResultToks.empty() || !ResultToks.back().is(tok::comma))
    return false;

  // Issue an extension diagnostic for the paste operator.
  if (HasPasteOperator)
    PP.Diag(ResultToks.back().getLocation(), diag::ext_paste_comma);

  // Remove the comma.
  ResultToks.pop_back();

  // If the comma was right after another paste (e.g. "X##,##__VA_ARGS__"),
  // then removal of the comma should produce a placemarker token (in C99
  // terms) which we model by popping off the previous ##, giving us a plain
  // "X" when __VA_ARGS__ is empty.
  if (!ResultToks.empty() && ResultToks.back().is(tok::hashhash))
    ResultToks.pop_back();

  // Never add a space, even if the comma, ##, or arg had a space.
  NextTokGetsSpace = false;
  return true;
}

/// Expand the arguments of a function-like macro so that we can quickly
/// return preexpanded tokens from Tokens.
void TokenLexer::ExpandFunctionArguments() {
  if (Macro->isVariadic() && PP.InBuildingMacroCache) {
    PP.ErrorsWhileCaching = true;
  }
  SmallVector<Token, 128> ResultToks;
  // Loop through 'Tokens', expanding them into ResultToks.  Keep
  // track of whether we change anything.  If not, no need to keep them.  If so,
  // we install the newly expanded sequence as the new 'Tokens' list.
  bool MadeChange = false;

  SmallVector<unsigned, 8> nonArgumentGuards;
  for (unsigned i = 0, e = NumTokens; i != e; ++i) {
    // If we found the stringify operator, get the argument stringified.  The
    // preprocessor already verified that the following token is a macro name
    // when the #define was parsed.
    const Token &CurTok = Tokens[i];

    if (i != 0 && !Tokens[i-1].is(tok::hashhash) && CurTok.hasLeadingSpace())
      NextTokGetsSpace = true;

    if (CurTok.isOneOf(tok::hash, tok::hashat) && !Tokens[i+1].isUnexpandableArg
        && !Tokens[i+1].is(tok::l_guard)) {
      int ArgNo = Macro->getArgumentNum(Tokens[i+1].getIdentifierInfo());
      assert(ArgNo != -1 && "Token following # is not an argument?");

      const Token * arg = ActualArgs->getUnexpArgument(ArgNo);


      bool canStringify = true;
      for (int j = 0; arg[j].isNot(tok::eof); j++) {
        if (arg[j].isUnexpandableArg) {
          canStringify = false;
          break;
        }
      }

      if (!canStringify) {
        //ResultToks.push_back(CurTok); // !!! this approach leads to errors!
        assert(PP.InBuildingMacroCache);
        if (PP.InBuildingMacroCache)
          PP.ErrorsWhileCaching = true;
        //llvm::errs() << "can't stringify!\n";
        continue;
      }

      SourceLocation ExpansionLocStart = CurTok.getLocation();
      SourceLocation ExpansionLocEnd = Tokens[i + 1].getLocation();
      if (WITH_LOCATIONS) {
        ExpansionLocStart =
                getExpansionLocForMacroDefLoc(CurTok.getLocation());
        ExpansionLocEnd =
                getExpansionLocForMacroDefLoc(Tokens[i + 1].getLocation());
      }

      Token Res;
      if (CurTok.is(tok::hash))   // Stringify
        Res = ActualArgs->getStringifiedArgument(ArgNo, PP,
                                                 ExpansionLocStart,
                                                 ExpansionLocEnd);
      else {
        // 'charify': don't bother caching these.
        Res = MacroArgs::StringifyArgument(arg,
                                           PP, true,
                                           ExpansionLocStart,
                                           ExpansionLocEnd);
      }
      Res.setFlag(Token::StringifiedInMacro);

      // The stringified/charified string leading space flag gets set to match
      // the #/#@ operator.
      if (NextTokGetsSpace)
        Res.setFlag(Token::LeadingSpace);

      ResultToks.push_back(Res);

      MadeChange = true;
      ++i;  // Skip arg name.
      NextTokGetsSpace = false;
      continue;
    }

    // Find out if there is a paste (##) operator before or after the token.
    bool NonEmptyPasteBefore =
      !ResultToks.empty() && ResultToks.back().is(tok::hashhash);
    bool PasteBefore = i != 0 && Tokens[i-1].is(tok::hashhash) && (!Tokens[i].isUnexpandableArg);
    bool PasteAfter = i+1 != e && Tokens[i+1].is(tok::hashhash) && (!Tokens[i].isUnexpandableArg);
    //assert(!NonEmptyPasteBefore || PasteBefore);

    // Otherwise, if this is not an argument token, just add the token to the
    // output buffer.
    IdentifierInfo *II = CurTok.getIdentifierInfo();
    int ArgNo = (II && !CurTok.isUnexpandableArg) ? Macro->getArgumentNum(II) : -1;
    if (ArgNo == -1) {
      // This isn't an argument, just add it.
      ResultToks.push_back(CurTok);

      if (CurTok.is(tok::l_guard)) {
        nonArgumentGuards.push_back(ResultToks.size() - 1);
      } else if (CurTok.is(tok::r_guard)) {
        nonArgumentGuards.pop_back();
      }

      if (NextTokGetsSpace) {
        ResultToks.back().setFlag(Token::LeadingSpace);
        NextTokGetsSpace = false;
      } else if (PasteBefore && !NonEmptyPasteBefore)
        ResultToks.back().clearFlag(Token::LeadingSpace);
      continue;
    }

    // An argument is expanded somehow, the result is different than the
    // input.
    MadeChange = true;

    // Otherwise, this is a use of the argument.

    // In Microsoft mode, remove the comma before __VA_ARGS__ to ensure there
    // are no trailing commas if __VA_ARGS__ is empty.
    if (!PasteBefore && ActualArgs->isVarargsElidedUse() &&
        MaybeRemoveCommaBeforeVaArgs(ResultToks,
                                     /*HasPasteOperator=*/false,
                                     Macro, ArgNo, PP)) {
      continue;
    }


    // If it is not the LHS/RHS of a ## operator, we must pre-expand the
    // argument and substitute the expanded tokens into the result.  This is
    // C99 6.10.3.1p1.
    if (!PasteBefore && !PasteAfter) {
      const Token *ResultArgToks;

      // Only preexpand the argument if it could possibly need it.  This
      // avoids some work in common cases.
      const Token *ArgTok = ActualArgs->getUnexpArgument(ArgNo);
      if (ActualArgs->ArgNeedsPreexpansion(ArgTok, PP)) {
        #ifdef DEBUG_PRINTS
        llvm::errs() << "getting arg prexpansion for ";
        DUMP_TOKEN_PTR(&CurTok, "\n");
        #endif
        ResultArgToks = &ActualArgs->getPreExpArgument(ArgNo, Macro, PP)[0];
      }
      else {
        #ifdef DEBUG_PRINTS
        llvm::errs() << "Use non-preexpanded tokens.\n";
        #endif
        ResultArgToks = ArgTok;  // Use non-preexpanded tokens.
      }



      // If the arg token expanded into anything, append it.
      if (ResultArgToks->isNot(tok::eof)) {
        unsigned FirstResult = ResultToks.size();
        unsigned NumToks = MacroArgs::getArgLength(ResultArgToks);
        if (NumToks == 3 && !nonArgumentGuards.empty() &&
            nonArgumentGuards.back() == FirstResult - 1 && i + 1 < e
            && Tokens[i+1].is(tok::r_guard) &&
                ResultArgToks[0].is(tok::l_guard)) {
          ResultArgToks++;
          NumToks -= 2;
        }

#ifdef DEBUG_PRINTS
        llvm::errs() << "Substituted arg: \n";
        for (int k = 0; k < NumToks; k++)
          DUMP_TOKEN_PTR(ResultArgToks + k);
        llvm::errs() << "\n\n";
#endif

        ResultToks.append(ResultArgToks, ResultArgToks+NumToks);

        // In Microsoft-compatibility mode, we follow MSVC's preprocessing
        // behavior by not considering single commas from nested macro
        // expansions as argument separators. Set a flag on the token so we can
        // test for this later when the macro expansion is processed.
        if (PP.getLangOpts().MSVCCompat && NumToks == 1 &&
            ResultToks.back().is(tok::comma)) {
          ResultToks.back().setFlag(Token::IgnoredComma);
        }

        // If the '##' came from expanding an argument, turn it into 'unknown'
        // to avoid pasting.

        for (unsigned i = FirstResult, e = ResultToks.size(); i != e; ++i) {
          Token &Tok = ResultToks[i];
          if (Tok.is(tok::hashhash) &&
                  !ResultToks[i-1].isUnexpandableArg && !ResultToks[i+1].isUnexpandableArg
              && ResultToks[i-1].isNot(tok::r_guard) && ResultToks[i+1].isNot(tok::l_guard)) {
            Tok.setKind(tok::unknown);
            Tok.setLocation(CurTok.getLocation());
          }
        }
        // TODO understand if this info should go to cache
        if(ExpandLocStart.isValid() && WITH_LOCATIONS) {
          updateLocForMacroArgTokens(CurTok.getLocation(),
                                     ResultToks.begin()+FirstResult,
                                     ResultToks.end());
        }

        // If any tokens were substituted from the argument, the whitespace
        // before the first token should match the whitespace of the arg
        // identifier.
        ResultToks[FirstResult].setFlagValue(Token::LeadingSpace,
                                             NextTokGetsSpace);
        NextTokGetsSpace = false;
      }
      continue;
    }

    // Okay, we have a token that is either the LHS or RHS of a paste (##)
    // argument.  It gets substituted as its non-pre-expanded tokens.
    const Token *ArgToks = ActualArgs->getUnexpArgument(ArgNo);
    unsigned NumToks = MacroArgs::getArgLength(ArgToks);
    if (NumToks) {  // Not an empty argument?
      // If this is the GNU ", ## __VA_ARGS__" extension, and we just learned
      // that __VA_ARGS__ expands to multiple tokens, avoid a pasting error when
      // the expander trys to paste ',' with the first token of the __VA_ARGS__
      // expansion.
      if (NonEmptyPasteBefore && ResultToks.size() >= 2 &&
          ResultToks[ResultToks.size()-2].is(tok::comma) &&
          (unsigned)ArgNo == Macro->getNumArgs()-1 &&
          Macro->isVariadic()) {
        // Remove the paste operator, report use of the extension.
        PP.Diag(ResultToks.pop_back_val().getLocation(), diag::ext_paste_comma);
      }

      size_t FirstResult = ResultToks.size();
      ResultToks.append(ArgToks, ArgToks+NumToks);

      // If the '##' came from expanding an argument, turn it into 'unknown'
      // to avoid pasting.
      for (unsigned i = FirstResult, e = ResultToks.size();
             i != e; ++i) {
        Token &Tok = ResultToks[i];
        Tok.setLocation(CurTok.getLocation());
        if (Tok.is(tok::hashhash)) {
          if (i+1 == e || i == 0 || (!ResultToks[i-1].isUnexpandableArg
            && !ResultToks[i+1].isUnexpandableArg && ResultToks[i-1].isNot(tok::r_guard)
                                                      && ResultToks[i+1].isNot(tok::l_guard)))
            // keep this as hashhash if it should concat actual args later
          Tok.setKind(tok::unknown); // but now it has one of the arguments unexpandable
        }
      }

      if (ExpandLocStart.isValid() && WITH_LOCATIONS) {
        updateLocForMacroArgTokens(CurTok.getLocation(),
                                   ResultToks.end()-NumToks, ResultToks.end());
      }

      // If this token (the macro argument) was supposed to get leading
      // whitespace, transfer this information onto the first token of the
      // expansion.
      //
      // Do not do this if the paste operator occurs before the macro argument,
      // as in "A ## MACROARG".  In valid code, the first token will get
      // smooshed onto the preceding one anyway (forming AMACROARG).  In
      // assembler-with-cpp mode, invalid pastes are allowed through: in this
      // case, we do not want the extra whitespace to be added.  For example,
      // we want ". ## foo" -> ".foo" not ". foo".
      if (NextTokGetsSpace) {
        ResultToks[ResultToks.size() - NumToks].setFlag(Token::LeadingSpace);
      }

      NextTokGetsSpace = false;
      continue;
    }

    // If an empty argument is on the LHS or RHS of a paste, the standard (C99
    // 6.10.3.3p2,3) calls for a bunch of placemarker stuff to occur.  We
    // implement this by eating ## operators when a LHS or RHS expands to
    // empty.
    if (PasteAfter) {
      // Discard the argument token and skip (don't copy to the expansion
      // buffer) the paste operator after it.
      ++i;
      continue;
    }

    // If this is on the RHS of a paste operator, we've already copied the
    // paste operator to the ResultToks list, unless the LHS was empty too.
    // Remove it.
    assert(PasteBefore);
    if (NonEmptyPasteBefore) {
      assert(ResultToks.back().is(tok::hashhash));
      ResultToks.pop_back();
    }

    // If this is the __VA_ARGS__ token, and if the argument wasn't provided,
    // and if the macro had at least one real argument, and if the token before
    // the ## was a comma, remove the comma.  This is a GCC extension which is
    // disabled when using -std=c99.
    if (ActualArgs->isVarargsElidedUse())
      MaybeRemoveCommaBeforeVaArgs(ResultToks,
                                   /*HasPasteOperator=*/true,
                                   Macro, ArgNo, PP);
    continue;
  }

  // If anything changed, install this as the new Tokens list.
  if (!ReadingFromExpansionCache) {
    if (MadeChange) {
      assert(!OwnsTokens && "This would leak if we already own the token list");
      // This is deleted in the dtor.
      NumTokens = ResultToks.size();

      // The tokens will be added to Preprocessor's cache and will be removed
      // when this TokenLexer finishes lexing them.
      Tokens = PP.cacheMacroExpandedTokens(this, ResultToks);

      // The preprocessor cache of macro expanded tokens owns these tokens,not us.
      OwnsTokens = false; // what for?
    }
    return;
  }


#ifdef DEBUG_PRINTS
  llvm::errs() << "After macro substitution: \n";
  for (auto iter = ResultToks.begin(); iter != ResultToks.end(); ++iter)
    DUMP_TOKEN_PTR(iter);
  llvm::errs() << "\n\n";
#endif
  SmallVector<Token, 128> tokens;
  SmallVector<unsigned, 8> guardsStack;
  SmallVector<bool, 8> hadArgSinceLastGuard;

  validateToks(ResultToks, ResultToks.size());
  for (unsigned i = 0, e = ResultToks.size(); i != e; ++i) {
    const Token &CurTok = ResultToks[i];
    tokens.push_back(CurTok);

    if (CurTok.isUnexpandableArg && !hadArgSinceLastGuard.empty()) {
      hadArgSinceLastGuard.back() = true;
    }

    if (CurTok.is(tok::r_guard)) {
      assert(!guardsStack.empty());
      unsigned start = guardsStack.pop_back_val();

      bool hadArg = hadArgSinceLastGuard.pop_back_val();

      if (!hadArgSinceLastGuard.empty() && !hadArgSinceLastGuard.back()) {
        hadArgSinceLastGuard.back() = hadArg;
      }

      const size_t size_before = start + hadArg;
      const size_t tokens_inside = tokens.size() - start;
      // else try fast pass: if it's just guard tok guard, and tok can't expand, go on
      if (hadArg || canExpandSomething(&*tokens.begin() + start + 1, tokens_inside - 2, PP)) {
        SmallVector<Token, 8> source;
        source.append(std::next(tokens.begin(), start + 1),
                      std::prev(tokens.end()));
        tokens.erase(std::next(tokens.begin(), start + hadArg), tokens.end());


        PP.EnterTokenStream(&*source.begin(), source.size(), false, false);
        Token Tok;
        PP.CurTokenLexer->lexingMode = GUARD_EXPANSION;
        PP.Lex(Tok);

        while (Tok.isNot(tok::eof)) {
          tokens.push_back(Tok);
          PP.Lex(Tok);
        }
      } else { // just remove guards
        //llvm::errs() << "hit with " << tokens_inside <<  " !\n";
        for (int j = 0; j < tokens_inside - 2; j++)
          tokens[start + j] = tokens[start + 1 + j];
        tokens.pop_back();
        tokens.pop_back();
      }


      // remove ## if following arg expanded into nothing
      if (size_before == tokens.size() && !tokens.empty() && tokens.back().is(tok::hashhash)) {
        tokens.pop_back();
        start--;
      }

      if (hadArg) {
        tokens.push_back(CurTok);
      } else if (start > 0 && tokens[start-1].is(tok::hash)) {
        SourceLocation ExpansionLocStart = tokens[start-1].getLocation();
        SourceLocation ExpansionLocEnd = tokens.back().isNot(tok::hash) ?
                                         tokens.back().getLocation() : ExpansionLocStart;
        assert(false);
        Token eof;
        eof.startToken();
        eof.setKind(tok::eof);
        tokens.push_back(eof);

        const Token *arg = &*tokens.begin() + start;
        Token Res = MacroArgs::StringifyArgument(arg,
                                             PP, false,
                                             ExpansionLocStart,
                                             ExpansionLocEnd);
        Res.setFlag(Token::StringifiedInMacro);
        tokens.erase(std::next(tokens.begin(), start - 1), tokens.end());
        tokens.push_back(Res);
      }
#ifdef DEBUG_PRINTS
      llvm::errs() << "After removing pair of guards: \n";
      for (auto iter = tokens.begin(); iter != tokens.end(); ++iter)
        DUMP_TOKEN_PTR(iter);
      llvm::errs() << "\n\n";
#endif
    } else if (CurTok.is(tok::l_guard)) {
      guardsStack.push_back(tokens.size() - 1);
      hadArgSinceLastGuard.push_back(false);
    }
  }

  NumTokens = tokens.size();
  Tokens = PP.cacheMacroExpandedTokens(this, tokens);
  OwnsTokens = false; // what for?

#ifdef DEBUG_PRINTS
  llvm::errs() << "After all substitutions:\n";
  for (auto iter = tokens.begin(); iter != tokens.end(); ++iter)
    DUMP_TOKEN_PTR(iter);
  llvm::errs() << "\n\n";
#endif
}

/// \brief Checks if two tokens form wide string literal.
static bool isWideStringLiteralFromMacro(const Token &FirstTok,
                                         const Token &SecondTok) {
  return FirstTok.is(tok::identifier) &&
         FirstTok.getIdentifierInfo()->isStr("L") && SecondTok.isLiteral() &&
         SecondTok.stringifiedInMacro();
}

/// Lex - Lex and return a token from this macro stream.
///
bool TokenLexer::Lex(Token &Tok) {
  // Lexing off the end of the macro, pop this macro off the expansion stack.
  if (isAtEnd()) {
    //llvm::errs() << "exit: " << reinterpret_cast<long long>(this) << "\n";
    // If this is a macro (not a token stream), mark the macro enabled now
    // that it is no longer being expanded.

    if (Macro && !Macro->isEnabled()) {
        Macro->EnableMacro();
    }

    if (lexingMode != NORMAL) {
      /*if (lexingMode == GUARD_EXPANSION)
        llvm::errs() << "GUARD_EXPANSION!\n";
      else
        llvm::errs() << "CACHE_CREATION!\n";*/

      Tok.startToken();

#ifdef DEBUG_PRINTS
      if (Macro && !MACRO_STACK.empty()) {
        MACRO_STACK.pop_back();
      }
#endif

      PP.HandleEndOfTokenLexer(Tok);
      Tok.setKind(tok::eof);
      return true;
    }

    Tok.startToken();
    Tok.setFlagValue(Token::StartOfLine , AtStartOfLine);
    Tok.setFlagValue(Token::LeadingSpace, HasLeadingSpace || NextTokGetsSpace);
    if (CurToken == 0)
      Tok.setFlag(Token::LeadingEmptyMacro);

    if (Macro && Macro->canBeCached() && !Macro->isExpansionCacheValid()
        && !PP.isBuildingMacroCache() && Macro->expandedTimes() > 0) {
      Macro->DisableMacro();
      makeCachedExpansion();

      if (!Macro->isEnabled())
        Macro->EnableMacro();
    }
#ifdef DEBUG_PRINTS
    if (Macro && !MACRO_STACK.empty()){
      MACRO_STACK.pop_back();
    }
#endif
    bool result = PP.HandleEndOfTokenLexer(Tok);
    
    return result;
  }
  // If this is the first token of the expanded result, we inherit spacing
  // properties later.
  bool isFirstToken = CurToken == 0;


  // Get the next token to return.
  Tok = Tokens[CurToken++];

  SourceManager &SM = PP.getSourceManager();

  bool TokenIsFromPaste = false;

  bool canPasteTokens = !isAtEnd() && !Tok.isUnexpandableArg &&
          !Tokens[CurToken+1].isUnexpandableArg && Tok.isNot(tok::r_guard)
            &&  Tokens[CurToken+1].isNot(tok::l_guard);

  // If this token is followed by a token paste (##) operator, paste the tokens!
  // Note that ## is a normal token when not expanding a macro.
  if (canPasteTokens && (Macro || lexingMode != NORMAL)  &&
      (Tokens[CurToken].is(tok::hashhash) ||
       // Special processing of L#x macros in -fms-compatibility mode.
       // Microsoft compiler is able to form a wide string literal from
       // 'L#macro_arg' construct in a function-like macro.
       (PP.getLangOpts().MSVCCompat &&
        isWideStringLiteralFromMacro(Tok, Tokens[CurToken])))) {
    // When handling the microsoft /##/ extension, the final token is
    // returned by PasteTokens, not the pasted token.

    //llvm::errs() << "pasting!\n";
    //DUMP_TOKEN_PTR(&Tok);
    //llvm::errs() << "\n";
    bool result = PasteTokens(Tok);
    if (Macro && !Macro->isExpansionCacheValid() && Tok.isAnyIdentifier()) {
      IdentifierInfo *II = Tok.getIdentifierInfo();
      if (!II->hasMacroDefinition())
        Macro->addNonMacroII(Tok.getIdentifierInfo());
      else
        MacroInfo::addDependency(Macro, PP.getMacroInfo(II));
    }

    if (result)
      return true;

    TokenIsFromPaste = true;
  }


  // If this is the first token, set the lexical properties of the token to
  // match the lexical properties of the macro identifier.
  if (isFirstToken) {
    Tok.setFlagValue(Token::StartOfLine , AtStartOfLine);
    Tok.setFlagValue(Token::LeadingSpace, HasLeadingSpace);
  } else {
    // If this is not the first token, we may still need to pass through
    // leading whitespace if we've expanded a macro.
    if (AtStartOfLine) Tok.setFlag(Token::StartOfLine);
    if (HasLeadingSpace) Tok.setFlag(Token::LeadingSpace);
  }
  AtStartOfLine = false;
  HasLeadingSpace = false;

  if (Tok.isUnexpandableArg)
    return true;

  // The token's current location indicate where the token was lexed from.  We
  // need this information to compute the spelling of the token, but any
  // diagnostics for the expanded token should appear as if they came from
  // ExpansionLoc.  Pull this information together into a new SourceLocation
  // that captures all of this.

  // Don't do this for token streams. and for reading from cache
  if (WITH_LOCATIONS && ExpandLocStart.isValid() &&
      // Check that the token's location was not already set properly.
      SM.isBeforeInSLocAddrSpace(Tok.getLocation(), MacroStartSLocOffset)) {
    SourceLocation instLoc;
    if (Tok.is(tok::comment)) {
      instLoc = SM.createExpansionLoc(Tok.getLocation(),
                                      ExpandLocStart,
                                      ExpandLocEnd,
                                      Tok.getLength());
    } else {
      instLoc = getExpansionLocForMacroDefLoc(Tok.getLocation());
    }

    Tok.setLocation(instLoc);
  }


  // Handle recursive expansion!
  if (!Tok.isAnnotation() && Tok.getIdentifierInfo() != nullptr) {
    // Change the kind of this identifier to the appropriate token kind, e.g.
    // turning "for" into a keyword.
    IdentifierInfo *II = Tok.getIdentifierInfo();

    Tok.setKind(II->getTokenID());
    // If this identifier was poisoned and from a paste, emit an error.  This
    // won't be handled by Preprocessor::HandleIdentifier because this is coming
    // from a macro expansion.
    if (II->isPoisoned() && TokenIsFromPaste) {
      PP.HandlePoisonedIdentifier(Tok);
    }

    if (!DisableMacroExpansion && II->isHandleIdentifierCase()) {
      //if (PP.getMacroInfo(II))

      if (Macro && !Macro->isExpansionCacheValid()) {
        if (II->hasMacroDefinition())
          MacroInfo::addDependency(Macro, PP.getMacroInfo(II));
        else if (Tok.isAnyIdentifier())
          Macro->addNonMacroII(II);
      }

      return PP.HandleIdentifier(Tok);
    }
  }
  // Otherwise, return a normal token.
  return true;
}

/// PasteTokens - Tok is the LHS of a ## operator, and CurToken is the ##
/// operator.  Read the ## and RHS, and paste the LHS/RHS together.  If there
/// are more ## after it, chomp them iteratively.  Return the result as Tok.
/// If this returns true, the caller should immediately return the token.
bool TokenLexer::PasteTokens(Token &Tok) {
  // MSVC: If previous token was pasted, this must be a recovery from an invalid
  // paste operation. Ignore spaces before this token to mimic MSVC output.
  // Required for generating valid UUID strings in some MS headers.
  if (PP.getLangOpts().MicrosoftExt && (CurToken >= 2) &&
      Tokens[CurToken - 2].is(tok::hashhash))
    Tok.clearFlag(Token::LeadingSpace);
  
  SmallString<128> Buffer;
  const char *ResultTokStrPtr = nullptr;
  SourceLocation StartLoc = Tok.getLocation();
  SourceLocation PasteOpLoc;
  do {
    // Consume the ## operator if any.
    PasteOpLoc = Tokens[CurToken].getLocation();
    if (Tokens[CurToken].is(tok::hashhash))
      ++CurToken;
    assert(!isAtEnd() && "No token on the RHS of a paste operator!");

    // Get the RHS token.
    const Token &RHS = Tokens[CurToken];

    // Allocate space for the result token.  This is guaranteed to be enough for
    // the two tokens.
    Buffer.resize(Tok.getLength() + RHS.getLength());

    // Get the spelling of the LHS token in Buffer.
    const char *BufPtr = &Buffer[0];
    bool Invalid = false;
    unsigned LHSLen = PP.getSpelling(Tok, BufPtr, &Invalid);
    if (BufPtr != &Buffer[0])   // Really, we want the chars in Buffer!
      memcpy(&Buffer[0], BufPtr, LHSLen);
    if (Invalid)
      return true;

    BufPtr = Buffer.data() + LHSLen;
    unsigned RHSLen = PP.getSpelling(RHS, BufPtr, &Invalid);
    if (Invalid)
      return true;
    if (RHSLen && BufPtr != &Buffer[LHSLen])
      // Really, we want the chars in Buffer!
      memcpy(&Buffer[LHSLen], BufPtr, RHSLen);

    // Trim excess space.
    Buffer.resize(LHSLen+RHSLen);

    // Plop the pasted result (including the trailing newline and null) into a
    // scratch buffer where we can lex it.
    Token ResultTokTmp;
    ResultTokTmp.startToken();

    // Claim that the tmp token is a string_literal so that we can get the
    // character pointer back from CreateString in getLiteralData().
    ResultTokTmp.setKind(tok::string_literal);
    PP.CreateString(Buffer, ResultTokTmp);
    SourceLocation ResultTokLoc = ResultTokTmp.getLocation();
    ResultTokStrPtr = ResultTokTmp.getLiteralData();

    // Lex the resultant pasted token into Result.
    Token Result;

    if (Tok.isAnyIdentifier() && RHS.isAnyIdentifier()) {
      // Common paste case: identifier+identifier = identifier.  Avoid creating
      // a lexer and other overhead.
      PP.IncrementPasteCounter(true);
      Result.startToken();
      Result.setKind(tok::raw_identifier);
      Result.setRawIdentifierData(ResultTokStrPtr);
      Result.setLocation(ResultTokLoc);
      Result.setLength(LHSLen+RHSLen);
    } else {
      PP.IncrementPasteCounter(false);

      assert(ResultTokLoc.isFileID() &&
             "Should be a raw location into scratch buffer");
      SourceManager &SourceMgr = PP.getSourceManager();
      FileID LocFileID = SourceMgr.getFileID(ResultTokLoc);

      bool Invalid = false;
      const char *ScratchBufStart
        = SourceMgr.getBufferData(LocFileID, &Invalid).data();
      if (Invalid)
        return false;

      // Make a lexer to lex this string from.  Lex just this one token.
      // Make a lexer object so that we lex and expand the paste result.
      Lexer TL(SourceMgr.getLocForStartOfFile(LocFileID),
               PP.getLangOpts(), ScratchBufStart,
               ResultTokStrPtr, ResultTokStrPtr+LHSLen+RHSLen);

      // Lex a token in raw mode.  This way it won't look up identifiers
      // automatically, lexing off the end will return an eof token, and
      // warnings are disabled.  This returns true if the result token is the
      // entire buffer.
      bool isInvalid = !TL.LexFromRawLexer(Result);

      // If we got an EOF token, we didn't form even ONE token.  For example, we
      // did "/ ## /" to get "//".
      isInvalid |= Result.is(tok::eof);

      // If pasting the two tokens didn't form a full new token, this is an
      // error.  This occurs with "x ## +"  and other stuff.  Return with Tok
      // unmodified and with RHS as the next token to lex.
      if (isInvalid) {
        // Explicitly convert the token location to have proper expansion
        // information so that the user knows where it came from.
        SourceManager &SM = PP.getSourceManager();
        SourceLocation Loc =
          SM.createExpansionLoc(PasteOpLoc, ExpandLocStart, ExpandLocEnd, 2);

        // Test for the Microsoft extension of /##/ turning into // here on the
        // error path.
        if (PP.getLangOpts().MicrosoftExt && Tok.is(tok::slash) &&
            RHS.is(tok::slash)) {
          HandleMicrosoftCommentPaste(Tok, Loc);
          return true;
        }

        // Do not emit the error when preprocessing assembler code.
        if (!PP.getLangOpts().AsmPreprocessor) {
          // If we're in microsoft extensions mode, downgrade this from a hard
          // error to an extension that defaults to an error.  This allows
          // disabling it.
          if (PP.isBuildingMacroCache()) {
            PP.setErrorsWhileCaching();
            break;
          } else {
            llvm::errs() << "not building macro cache\n";
          }

          PP.Diag(Loc, PP.getLangOpts().MicrosoftExt ? diag::ext_pp_bad_paste_ms
                                                     : diag::err_pp_bad_paste)
              << Buffer;
        }

        // An error has occurred so exit loop.
        break;
      }

      // Turn ## into 'unknown' to avoid # ## # from looking like a paste
      // operator.
      if (Result.is(tok::hashhash))
        Result.setKind(tok::unknown);
    }

    // Transfer properties of the LHS over the Result.
    Result.setFlagValue(Token::StartOfLine , Tok.isAtStartOfLine());
    Result.setFlagValue(Token::LeadingSpace, Tok.hasLeadingSpace());
    
    // Finally, replace LHS with the result, consume the RHS, and iterate.
    ++CurToken;
    Tok = Result;
  } while (!isAtEnd() && Tokens[CurToken].is(tok::hashhash) &&
          !Tokens[CurToken + 1].isUnexpandableArg && Tokens[CurToken + 1].isNot(tok::l_guard));

  SourceLocation EndLoc = Tokens[CurToken - 1].getLocation();

  // The token's current location indicate where the token was lexed from.  We
  // need this information to compute the spelling of the token, but any
  // diagnostics for the expanded token should appear as if the token was
  // expanded from the full ## expression. Pull this information together into
  // a new SourceLocation that captures all of this.
  SourceManager &SM = PP.getSourceManager();

  if (WITH_LOCATIONS) {
    if (StartLoc.isFileID())
      StartLoc = getExpansionLocForMacroDefLoc(StartLoc);
    if (EndLoc.isFileID())
      EndLoc = getExpansionLocForMacroDefLoc(EndLoc);

    FileID MacroFID = SM.getFileID(MacroExpansionStart);
    while (SM.getFileID(StartLoc) != MacroFID) {
      StartLoc = SM.getImmediateExpansionRange(StartLoc).first;
    }

    while (SM.getFileID(EndLoc) != MacroFID)
      EndLoc = SM.getImmediateExpansionRange(EndLoc).second;

    Tok.setLocation(SM.createExpansionLoc(Tok.getLocation(), StartLoc, EndLoc,
                                          Tok.getLength()));
  } else {
    Tok.setLocation(Tokens[CurToken - 1].getLocation());
  }

  // Now that we got the result token, it will be subject to expansion.  Since
  // token pasting re-lexes the result token in raw mode, identifier information
  // isn't looked up.  As such, if the result is an identifier, look up id info.
  if (Tok.is(tok::raw_identifier)) {
    // Look up the identifier info for the token.  We disabled identifier lookup
    // by saying we're skipping contents, so we need to do this manually.
    PP.LookUpIdentifierInfo(Tok);
  }
  return false;
}

/// isNextTokenLParen - If the next token lexed will pop this macro off the
/// expansion stack, return 2.  If the next unexpanded token is a '(', return
/// 1, otherwise return 0.
unsigned TokenLexer::isNextTokenLParen() const {
  // Out of tokens?
  // TODO here need proper answer while using cache
  if (isAtEnd()) {
    if (lexingMode == NORMAL)
      return 2;
    return 0;
  }

  return Tokens[CurToken].is(tok::l_paren);
}

/// isParsingPreprocessorDirective - Return true if we are in the middle of a
/// preprocessor directive.
bool TokenLexer::isParsingPreprocessorDirective() const {
  // TODO here need proper answer while using cache
  return Tokens[NumTokens-1].is(tok::eod) && !isAtEnd();
}

/// HandleMicrosoftCommentPaste - In microsoft compatibility mode, /##/ pastes
/// together to form a comment that comments out everything in the current
/// macro, other active macros, and anything left on the current physical
/// source line of the expanded buffer.  Handle this by returning the
/// first token on the next line.
void TokenLexer::HandleMicrosoftCommentPaste(Token &Tok, SourceLocation OpLoc) {
  PP.Diag(OpLoc, diag::ext_comment_paste_microsoft);

  // We 'comment out' the rest of this macro by just ignoring the rest of the
  // tokens that have not been lexed yet, if any.

  // Since this must be a macro, mark the macro enabled now that it is no longer
  // being expanded.
  assert(Macro && "Token streams can't paste comments");
  Macro->EnableMacro();

  PP.HandleMicrosoftCommentPaste(Tok);
}

/// \brief If \arg loc is a file ID and points inside the current macro
/// definition, returns the appropriate source location pointing at the
/// macro expansion source location entry, otherwise it returns an invalid
/// SourceLocation.
SourceLocation
TokenLexer::getExpansionLocForMacroDefLoc(SourceLocation loc) const {
  assert(ExpandLocStart.isValid() && MacroExpansionStart.isValid() &&
         "Not appropriate for token streams");
  assert(loc.isValid() && loc.isFileID());
  
  SourceManager &SM = PP.getSourceManager();
  assert(SM.isInSLocAddrSpace(loc, MacroDefStart, MacroDefLength) &&
         "Expected loc to come from the macro definition");

  unsigned relativeOffset = 0;
  SM.isInSLocAddrSpace(loc, MacroDefStart, MacroDefLength, &relativeOffset);
  return MacroExpansionStart.getLocWithOffset(relativeOffset);
}

/// \brief Finds the tokens that are consecutive (from the same FileID)
/// creates a single SLocEntry, and assigns SourceLocations to each token that
/// point to that SLocEntry. e.g for
///   assert(foo == bar);
/// There will be a single SLocEntry for the "foo == bar" chunk and locations
/// for the 'foo', '==', 'bar' tokens will point inside that chunk.
///
/// \arg begin_tokens will be updated to a position past all the found
/// consecutive tokens.
static void updateConsecutiveMacroArgTokens(SourceManager &SM,
                                            SourceLocation InstLoc,
                                            Token *&begin_tokens,
                                            Token * end_tokens) {
  assert(begin_tokens < end_tokens);

  SourceLocation FirstLoc = begin_tokens->getLocation();
  SourceLocation CurLoc = FirstLoc;

  // Compare the source location offset of tokens and group together tokens that
  // are close, even if their locations point to different FileIDs. e.g.
  //
  //  |bar    |  foo | cake   |  (3 tokens from 3 consecutive FileIDs)
  //  ^                    ^
  //  |bar       foo   cake|     (one SLocEntry chunk for all tokens)
  //
  // we can perform this "merge" since the token's spelling location depends
  // on the relative offset.

  Token *NextTok = begin_tokens + 1;
  for (; NextTok < end_tokens; ++NextTok) {
    SourceLocation NextLoc = NextTok->getLocation();
    if (CurLoc.isFileID() != NextLoc.isFileID())
      break; // Token from different kind of FileID.

    int RelOffs;
    if (!SM.isInSameSLocAddrSpace(CurLoc, NextLoc, &RelOffs))
      break; // Token from different local/loaded location.
    // Check that token is not before the previous token or more than 50
    // "characters" away.
    if (RelOffs < 0 || RelOffs > 50)
      break;
    CurLoc = NextLoc;
  }

  // For the consecutive tokens, find the length of the SLocEntry to contain
  // all of them.
  Token &LastConsecutiveTok = *(NextTok-1);
  int LastRelOffs = 0;
  SM.isInSameSLocAddrSpace(FirstLoc, LastConsecutiveTok.getLocation(),
                           &LastRelOffs);
  unsigned FullLength = LastRelOffs + LastConsecutiveTok.getLength();

  // Create a macro expansion SLocEntry that will "contain" all of the tokens.
  SourceLocation Expansion =
      SM.createMacroArgExpansionLoc(FirstLoc, InstLoc,FullLength);

  // Change the location of the tokens from the spelling location to the new
  // expanded location.
  for (; begin_tokens < NextTok; ++begin_tokens) {
    Token &Tok = *begin_tokens;
    int RelOffs = 0;
    SM.isInSameSLocAddrSpace(FirstLoc, Tok.getLocation(), &RelOffs);
    Tok.setLocation(Expansion.getLocWithOffset(RelOffs));
  }
}

/// \brief Creates SLocEntries and updates the locations of macro argument
/// tokens to their new expanded locations.
///
/// \param ArgIdDefLoc the location of the macro argument id inside the macro
/// definition.
/// \param Tokens the macro argument tokens to update.
void TokenLexer::updateLocForMacroArgTokens(SourceLocation ArgIdSpellLoc,
                                            Token *begin_tokens,
                                            Token *end_tokens) {
  SourceManager &SM = PP.getSourceManager();

  SourceLocation InstLoc =
      getExpansionLocForMacroDefLoc(ArgIdSpellLoc);
  
  while (begin_tokens < end_tokens) {
    // If there's only one token just create a SLocEntry for it.
    if (end_tokens - begin_tokens == 1) {
      Token &Tok = *begin_tokens;
      Tok.setLocation(SM.createMacroArgExpansionLoc(Tok.getLocation(),
                                                    InstLoc,
                                                    Tok.getLength()));
      return;
    }

    updateConsecutiveMacroArgTokens(SM, InstLoc, begin_tokens, end_tokens);
  }
}

void TokenLexer::PropagateLineStartLeadingSpaceInfo(Token &Result) {
  AtStartOfLine = Result.isAtStartOfLine();
  HasLeadingSpace = Result.hasLeadingSpace();
}

void TokenLexer::makeCachedExpansion() {
  //if (WITH_LOCATIONS)
  //  return;

  PP.InBuildingMacroCache = true;

  if (Macro->isVariadic()) {
    Macro->setCanBeCached(false);
    PP.InBuildingMacroCache = false;
    return;
  }

#ifdef DEBUG_PRINTS
  llvm::errs() << "makeCachedExpansion() for ";
  assert(MACRO_STACK.size());
  DUMP_TOKEN_PTR(MACRO_STACK.rbegin(), "\n");
  llvm::errs() << "input:\n";
#endif

  SmallVector<Token, 8> tokens;
  tokens.reserve(Macro->getNumTokens());

  size_t bufSize = Macro->tokens().size();
  for (size_t i = 0; i < bufSize; i++) {
    if ((i == 0 || !tokenForbidsEpansion(tokens.back())) &&
            getArgNum(Macro->tokens()[i], Macro) != -1 &&
            (i + 1 == bufSize || !tokenForbidsEpansion(Macro->tokens()[i + 1]))) {
      Token guard;
      guard.startToken();
      guard.setKind(tok::l_guard);
      guard.setLocation(Macro->tokens()[i].getLocation());
      tokens.push_back(guard);
      tokens.push_back(Macro->tokens()[i]);
      tokens.back().isUnexpandableArg = true;
      guard.setKind(tok::r_guard);
      tokens.push_back(guard);
      continue;
    }

    tokens.push_back(Macro->tokens()[i]);
    if (getArgNum(tokens.back(), Macro) != -1)
      tokens.back().isUnexpandableArg = true;
  }

#ifdef DEBUG_PRINTS
  for (auto tok = tokens.begin(); tok != tokens.end(); ++tok){
    DUMP_TOKEN_PTR(tok);
  }
  llvm::errs() << "\n\n";
#endif

  SmallVector<Token, 8> Result;
  PP.EnterTokenStream(&*tokens.begin(), tokens.size(), false, false);
  bool oldPPDisableExpansion = PP.DisableMacroExpansion;

  PP.DisableMacroExpansion = false;
  PP.CurTokenLexer->lexingMode = CACHE_CREATION;

  do {
    Result.push_back(Token());
    Token &Tok = Result.back();
    PP.Lex(Tok);
    Tok.isUnexpandableArg = false;
  } while (Result.back().isNot(tok::eof));
  if (PP.ErrorsWhileCaching) {
    llvm::errs() << "Errors while caching! Exiting...\n";
    PP.ErrorsWhileCaching = false;
    Macro->setCanBeCached(false);
    PP.InBuildingMacroCache = false;
    PP.DisableMacroExpansion = oldPPDisableExpansion;
    return;
  }
  Result.pop_back();
  assert(lexingMode != GUARD_EXPANSION && "Sanity check failed!");

  Macro->resetCache(std::move(Result));
#ifdef DEBUG_PRINTS
  llvm::errs() << "Result for ";
  DUMP_TOKEN_PTR(MACRO_STACK.rbegin(), ":\n");

  for (auto tok = Macro->getExpansionCache().begin(); tok != Macro->getExpansionCache().end(); ++tok){
    DUMP_TOKEN_PTR(tok);
  }
  llvm::errs() << "\n\n";
#endif

  PP.DisableMacroExpansion = oldPPDisableExpansion;
  Macro->setExpansionCacheValid(true);
  //llvm::errs() << "END of makeCachedExpansion()\n";
  PP.InBuildingMacroCache = false;
}
