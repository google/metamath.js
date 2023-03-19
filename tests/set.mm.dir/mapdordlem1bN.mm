include "lcfl1lem.mm"

theorem mapdordlem1bN
  let cC: class C
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cL: class L
  let cO: class O
  assume mapdordlem1b.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }

  disjoint F g
  disjoint J g
  disjoint L g
  disjoint O g
  assert |- ( J e. C <-> ( J e. F /\ ( O ` ( O ` ( L ` J ) ) ) = ( L ` J ) ) )

  proof
    cC
    vg
    cF
    cJ
    cL
    cO
    mapdordlem1b.c
    lcfl1lem
end
