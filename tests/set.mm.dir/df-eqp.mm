
axiom df-eqp
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  assert |- ~Qp = ( p e. Prime |-> { <. f , g >. | ( { f , g } C_ ( ZZ ^m ZZ ) /\ A. n e. ZZ sum_ k e. ( ZZ>= ` -u n ) ( ( ( f ` -u k ) - ( g ` -u k ) ) / ( p ^ ( k + ( n + 1 ) ) ) ) e. ZZ ) } )
end
