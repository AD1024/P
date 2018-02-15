using System;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using NUnit.Framework;

namespace UnitTests
{
    internal static class Constants
    {
        internal const string CategorySeparator = " | ";
        internal const string CRuntimeTesterDirectoryName = "PrtTester";
        internal const string NewLinePattern = @"\r\n|\n\r|\n|\r";
        internal const string XmlProfileFileName = "TestProfile.xml";
        internal const string PSolutionFileName = "P.sln";
        internal const string TestDirectoryName = "Tst";
        internal const string CTesterExecutableName = "tester.exe";
        internal const string CTesterVsProjectName = "Tester.vcxproj";
        internal const string CorrectOutputFileName = "acc_0.txt";
        internal const string TestConfigFileName = "testconfig.txt";
        internal const string DiffTool = "kdiff3";
        internal const string DisplayDiffsFile = "display-diffs.bat";
        internal const string ActualOutputFileName = "check-output.log";
        internal const string FrontEndRegressionFileName = "frontend-regression.txt";
#if DEBUG
        internal const string Configuration = "Debug";
#else
        internal const string Configuration = "Release";
#endif
        internal static string Platform { get; } = Environment.Is64BitProcess ? "x64" : "x86";

        private static readonly Lazy<string> LazySolutionDirectory = new Lazy<string>(
            () =>
            {
                string assemblyPath = Path.GetDirectoryName(Assembly.GetEntryAssembly().Location);
                string assemblyDirectory = Path.GetDirectoryName(assemblyPath);
                Contract.Assert(assemblyDirectory != null);
                for (var dir = new DirectoryInfo(assemblyDirectory); dir != null; dir = dir.Parent)
                {
                    if (File.Exists(Path.Combine(dir.FullName, PSolutionFileName)))
                    {
                        return dir.FullName;
                    }
                }

                throw new FileNotFoundException();
            });

        internal static string SolutionDirectory => LazySolutionDirectory.Value;

        internal static string TestDirectory => Path.Combine(SolutionDirectory, TestDirectoryName);

        internal static bool ResetTests => bool.Parse(TestContext.Parameters["ResetTests"]);
        internal static bool RunPc => bool.Parse(TestContext.Parameters["RunPc"]);
        internal static bool RunPrt => bool.Parse(TestContext.Parameters["RunPrt"]);
        internal static bool RunPt => bool.Parse(TestContext.Parameters["RunPt"]);
        internal static bool RunZing => bool.Parse(TestContext.Parameters["RunZing"]);
        internal static bool RunAll => bool.Parse(TestContext.Parameters["RunAll"]);
        internal static bool PtWithPSharp => bool.Parse(TestContext.Parameters["PtWithPSharp"]);

        internal static string TestResultsDirectory { get; } = Path.Combine(TestDirectory, $"TestResult_{Configuration}_{Platform}");
    }
}