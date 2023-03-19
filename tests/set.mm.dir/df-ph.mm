
axiom df-ph
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  assert |- CPreHilOLD = ( NrmCVec i^i { <. <. g , s >. , n >. | A. x e. ran g A. y e. ran g ( ( ( n ` ( x g y ) ) ^ 2 ) + ( ( n ` ( x g ( -u 1 s y ) ) ) ^ 2 ) ) = ( 2 x. ( ( ( n ` x ) ^ 2 ) + ( ( n ` y ) ^ 2 ) ) ) } )
end
