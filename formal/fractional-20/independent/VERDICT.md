# Independent verdict before reading the supplied encoder

The full 23-slot instance for m=16, bound=4 is UNSAT. CaDiCaL returned UNSAT
after 350.50 seconds CPU / 361.45 seconds wall time, using a reported maximum
resident set of 391.89 MB. The separately written RUP-fragment LRAT checker
accepted the certificate in 19.1004 seconds, verifying 2,418,926 additions and
3,943,654 deletions. No RAT step was used.

Both positive controls passed graph-level and original-CNF validation:
15 selected edges at bound 4, and 20 selected edges at bound 5. Their graphs
are saved as `control15.graph.txt` and `control20.graph.txt`.

This computationally verifies the stronger finite statement, subject to the
documented encoding, compiler and independent checker trust base. It is not a
Lean proof of Proposition D. No substantive error in D has been found.

SHA256 of the full input CNF:
`05F89B4089DDB6668E1FC5DC8873FC807DE1A487BF81A9DE60A8628E0420F8D4`

SHA256 of its LRAT certificate:
`6E60536ABFA146C11EF7D7F9F7072AB20ADAA4EEDA836F41F0CEF57C994FC3D2`

The supplied `exp49_frac_core.py` was first opened only after the full
independent certificate replay succeeded.
