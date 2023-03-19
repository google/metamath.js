
axiom df-cncf
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  assert |- -cn-> = ( a e. ~P CC , b e. ~P CC |-> { f e. ( b ^m a ) | A. x e. a A. e e. RR+ E. d e. RR+ A. y e. a ( ( abs ` ( x - y ) ) < d -> ( abs ` ( ( f ` x ) - ( f ` y ) ) ) < e ) } )
end
