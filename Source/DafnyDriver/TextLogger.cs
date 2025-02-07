using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class TextLogger {
  private TextWriter tw;
  private TextWriter outWriter;
  private ProofDependencyManager depManager;

  public TextLogger(ProofDependencyManager depManager, TextWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  public void LogResults(List<(Implementation, VerificationResult)> verificationResults) {
    var orderedResults =
      verificationResults.OrderBy(vr =>
        (vr.Item1.tok.filename, vr.Item1.tok.line, vr.Item1.tok.col));
    foreach (var (implementation, result) in orderedResults) {
      tw.WriteLine("");
      tw.WriteLine($"Results for {implementation.VerboseName}");
      tw.WriteLine($"  Overall outcome: {result.Outcome}");
      tw.WriteLine($"  Overall time: {result.End - result.Start}");
      tw.WriteLine($"  Overall resource count: {result.ResourceCount}");
      // It doesn't seem possible to get a result with zero VCResults, but being careful with nulls just in case :)
      var maximumTime = result.VCResults.MaxBy(r => r.runTime)?.runTime.ToString() ?? "N/A";
      var maximumRC = result.VCResults.MaxBy(r => r.resourceCount)?.resourceCount.ToString() ?? "N/A";
      tw.WriteLine($"  Maximum assertion batch time: {maximumTime}");
      tw.WriteLine($"  Maximum assertion batch resource count: {maximumRC}");
      foreach (var vcResult in result.VCResults.OrderBy(r => r.vcNum)) {
        tw.WriteLine("");
        tw.WriteLine($"  Assertion batch {vcResult.vcNum}:");
        tw.WriteLine($"    Outcome: {vcResult.outcome}");
        tw.WriteLine($"    Duration: {vcResult.runTime}");
        tw.WriteLine($"    Resource count: {vcResult.resourceCount}");
        tw.WriteLine("");
        tw.WriteLine("    Assertions:");
        foreach (var cmd in vcResult.asserts) {
          tw.WriteLine(
            $"      {((IToken)cmd.tok).filename}({cmd.tok.line},{cmd.tok.col}): {cmd.Description.SuccessDescription}");
        }

        if (vcResult.coveredElements.Any()) {
          tw.WriteLine("");
          tw.WriteLine("    Proof dependencies:");
          var fullDependencies =
            vcResult
            .coveredElements
            .Select(depManager.GetFullIdDependency)
            .OrderBy(dep => (dep.RangeString(), dep.Description));
          foreach (var dep in fullDependencies) {
            tw.WriteLine($"      {dep.RangeString()}: {dep.Description}");
          }
        }

      }
    }
    tw.Flush();
  }
}
