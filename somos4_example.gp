\\ Example driver for the bounded companion.
\\
\\ Usage from the repository root:
\\   gp -q somos4_example.gp > verification_report.txt

read("somos4_theta_companion.gp");
somos4_reference_run();
quit;