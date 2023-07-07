using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AbstractTypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICanFormat, IHasDocstring {
  public override string WhatKind { get { return "abstract type"; } }
  public override bool CanBeRevealed() { return true; }
  public readonly TypeParameter.TypeParameterCharacteristics Characteristics;
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
  }

  public AbstractTypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, TypeParameter.TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, parentTraits) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeArgs != null);
    Characteristics = characteristics;
    this.NewSelfSynonym();
  }

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override bool AcceptThis => true;
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var indent2 = indentBefore + formatter.SpaceTab;
    var typeArgumentIndent = indent2;
    var commaIndent = indent2;
    var rightIndent = indent2;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "type": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "=": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetDelimiterInsideIndentedRegions(token, indent2);
            } else {
              formatter.SetAlign(indent2, token, out typeArgumentIndent, out _);
            }

            break;
          }
        case "<": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, typeArgumentIndent);
              commaIndent = typeArgumentIndent;
              rightIndent = commaIndent + formatter.SpaceTab;
            } else {
              formatter.SetAlign(typeArgumentIndent + formatter.SpaceTab, token, out rightIndent, out commaIndent);
            }

            break;
          }
        case ">": {
            formatter.SetIndentations(token.Prev, below: rightIndent);
            formatter.SetClosingIndentedRegionAligned(token, rightIndent, typeArgumentIndent);
            break;
          }
        case ",": {
            formatter.SetIndentations(token, rightIndent, commaIndent, rightIndent);
            break;
          }
        case ";": {
            break;
          }
        case "{": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "}": {
            formatter.SetClosingIndentedRegion(token, indentBefore);
            break;
          }
      }
    }

    if (EndToken.TrailingTrivia.Trim() == "") {
      formatter.SetIndentations(EndToken, below: indentBefore);
    }

    return true;
  }

  protected override string GetTriviaContainingDocstring() {
    IToken openingBlock = null;
    foreach (var token in OwnedTokens) {
      if (token.val == "{") {
        openingBlock = token;
      }
    }

    if (openingBlock != null && openingBlock.Prev.TrailingTrivia.Trim() != "") {
      return openingBlock.Prev.TrailingTrivia;
    }

    if (openingBlock == null && EndToken.TrailingTrivia.Trim() != "") {
      return EndToken.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}