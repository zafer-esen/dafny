﻿using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.GutterStatus;

[Collection("Sequential Collection")]
public class SimpleLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxTestExecutionTimeMs = 10000;

  // To add a new test, just call VerifyTrace on a given program,
  // the test will fail and give the correct output that can be use for the test
  // Add '//Next<n>:' to edit a line multiple times

  [Fact]
  public async Task GitIssue3821GutterIgnoredProblem() {
    await VerifyTrace(@"
 | :function fib(n: nat): nat {
 | :  if n <= 1 then n else fib(n-1) + fib(n-2)
 | :}
 | :
[ ]:method {:rlimit 1} Test(s: seq<nat>)
[=]:  requires |s| >= 1 && s[0] >= 0 {
[=]:  assert fib(10) == 1; assert {:split_here} s[0] >= 0;
[ ]:}", intermediates: false);
  }

  [Fact]
  public async Task NoGutterNotificationsReceivedWhenTurnedOff() {
    var source = @"
method Foo() ensures false { } ";
    await SetUp(options => {
      options.Set(ServerCommand.LineVerificationStatus, false);
    });

    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.False(verificationStatusGutterReceiver.HasPendingNotifications);
  }

  [Fact]
  public async Task EnsureEmptyMethodDisplayVerified() {
    await VerifyTrace(@"
 .  | :method x() {
 .  | :  // Nothing here
 .  | :}");
  }

  [Fact/*, Timeout(MaxTestExecutionTimeMs)*/]
  public async Task EnsureVerificationGutterStatusIsWorking() {
    await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
    await VerifyTrace(@"
 .  |  |  |  I  I  |  | :predicate Ok() {
 .  |  |  |  I  I  |  | :  true
 .  |  |  |  I  I  |  | :}
    |  |  |  I  I  |  | :
 .  S [S][ ][I][I][S] | :method Test(x: bool) returns (i: int)
 .  S [=][=][-][-][~] | :   ensures i == 2
 .  S [S][ ][I][I][S] | :{
 .  S [S][ ][I][I][S] | :  if x {
 .  S [S][ ][I][I][S] | :    i := 2;
 .  S [=][=][-][-][~] | :  } else {
 .  S [S][ ]/!\[I][S] | :    i := 1; //Next1:   i := /; //Next2:    i := 2;
 .  S [S][ ][I][I][S] | :  }
 .  S [S][ ][I][I][S] | :}
    |  |  |  I  I  |  | :    
 .  |  |  |  I  I  |  | :predicate OkBis() {
 .  |  |  |  I  I  |  | :  false
 .  |  |  |  I  I  |  | :}");
  }
  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsuresItWorksForSubsetTypes() {
    await VerifyTrace(@"
    |  |  |  I  I  |  |  |  I  I  |  |  | :
 .  |  |  |  I  I  |  |  |  I  I  |  |  | :ghost const maxId := 200;
    |  |  |  I  I  |  |  |  I  I  |  |  | :
 .  |  |  |  I  I  |  |  |  I  I  |  |  | :ghost predicate isIssueIdValid(issueId: int) {
 .  |  |  |  I  I  |  |  |  I  I  |  |  | :  101 <= issueId < maxId
 .  |  |  |  I  I  |  |  |  I  I  |  |  | :}
    |  |  |  I  I  |  |  |  I  I  |  |  | :
 .  S  S  |  I  .  S  S [=] I  .  S  S  | :type IssueId = i : int | isIssueIdValid(i)
 .  S  |  |  I  .  S  | [=] I  .  S  |  | :  witness 101 //Next1:   witness 99 //Next2:   witness 101 ");
  }

  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsureItWorksForPostconditionsRelatedOutside() {
    await VerifyTrace(@"
 .  |  |  | :predicate F(i: int) {
 .  |  |  | :  false // Should not be highlighted in gutter.
 .  |  |  | :}
    |  |  | :
 .  S [S][ ]:method H()
 .  S [=][=]:  ensures F(1)
 .  S [=][=]:{
 .  S [S][ ]:}");
  }

  [Fact(Timeout = MaxTestExecutionTimeMs * 10)]
  public async Task EnsureNoAssertShowsVerified() {
    for (var i = 0; i < 10; i++) {
      await VerifyTrace(@"
 .  |  |  |  I  | :predicate P(x: int)
    |  |  |  I  | :
 .  S [S][ ][I] | :method Main() {
 .  S [=][=][I] | :  ghost var x :| P(x); //Next:  ghost var x := 1;
 .  S [S][ ][I] | :}
                | :");
    }
  }

  [Fact(Timeout = MaxTestExecutionTimeMs)]
  public async Task EnsureEmptyDocumentIsVerified() {
    await VerifyTrace(@"
 | :class A {
 | :}
 | :");
  }


  [Fact/*, Timeout(MaxTestExecutionTimeMs)*/]
  public async Task EnsuresEmptyDocumentWithParseErrorShowsError() {
    await VerifyTrace(@"
/!\:class A {/
   :}
   :");
  }

  [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
  public async Task EnsuresDefaultArgumentsShowsError() {
    await VerifyTrace(@"
 .  S [~][=]:datatype D = T(i: nat := -2)");
  }

  [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
  public async Task TopLevelConstantsHaveToBeVerifiedAlso() {
    await VerifyTrace(@"
    |  |  | :// The following should trigger only one error
 .  |  |  | :ghost const a := [1, 2];
    |  |  | :
 .  S [~][=]:ghost const b := a[-1];");
  }

  [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
  public async Task EnsuresAddingNewlinesMigratesPositions() {
    await VerifyTrace(@"
 .  S [S][ ][I][S][ ][I][S][ ]:method f(x: int) {
 .  S [S][ ][I][S][ ][I][S][ ]:  //Next1:\n  //Next2:\n  
 .  S [=][=][I][S][ ][I][S][ ]:  assert x == 2; }
            [-][~][=][I][S][ ]:
                     [-][~][=]:");
  }

  [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
  public async Task EnsuresWorkWithInformationsAsWell() {
    await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
    await VerifyTrace(@"
 .  S [S][ ][I][S][S][ ]:method f(x: int) returns (y: int)
 .  S [S][ ][I][S][S][ ]:ensures
 .  S [=][=][-][~][=][=]:  x > 3 { y := x;
 .  S [S][ ][I][S][S][ ]:  //Next1:\n
 .  S [=][=][-][~][=][ ]:  while(y <= 1) invariant y >= 2 {
 .  S [S][ ][-][~][~][=]:    y := y + 1;
 .  S [S][ ][I][S][S][ ]:  }
 .  S [S][ ][I][S][S][ ]:}
            [I][S][S][ ]:");
  }

  [Fact]
  public async Task EnsureMultilineAssertIsCorreclyHandled() {
    await VerifyTrace(@"
 .  S [S][ ]:method x() {
 .  S [=][=]:  assert false
 .  S [=][=]:    || false;
 .  S [S][ ]:}");
  }

  [Fact]
  public async Task EnsureBodylessMethodsAreCovered() {
    await VerifyTrace(@"
 .  |  |  | :method test() {
 .  |  |  | :}
    |  |  | :
 .  S [S][ ]:method {:extern} test3(a: nat, b: nat)
 .  S [S][ ]:  ensures true
 .  S [=][=]:  ensures test2(a - b)
 .  S [S][ ]:  ensures true
 .  S [O][O]:  ensures test2(a - b)
 .  S [S][ ]:  ensures true
    |  |  | :
 .  |  |  | :predicate test2(x: nat) {
 .  |  |  | :  true
 .  |  |  | :}");
  }


  [Fact]
  public async Task EnsureBodylessFunctionsAreCovered() {
    await VerifyTrace(@"
 .  |  |  | :method test() {
 .  |  |  | :}
    |  |  | :
 .  S [S][ ]:function {:extern} test4(a: nat, b: nat): nat
 .  S [S][ ]:  ensures true
 .  S [=][=]:  ensures test2(a - b)
 .  S [S][ ]:  ensures true
 .  S [O][O]:  ensures test2(a - b)
 .  S [S][ ]:  ensures true
    |  |  | :
 .  |  |  | :predicate test2(x: nat) {
 .  |  |  | :  true
 .  |  |  | :}");
  }

  public SimpleLinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output) {
  }
}
