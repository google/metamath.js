
axiom df-msr
  let vz: setvar z
  let vt: setvar t
  let vh: setvar h
  let vs: setvar s
  let va: setvar a
  assert |- mStRed = ( t e. _V |-> ( s e. ( mPreSt ` t ) |-> [_ ( 2nd ` ( 1st ` s ) ) / h ]_ [_ ( 2nd ` s ) / a ]_ <. ( ( 1st ` ( 1st ` s ) ) i^i [_ U. ( ( mVars ` t ) " ( h u. { a } ) ) / z ]_ ( z X. z ) ) , h , a >. ) )
end
