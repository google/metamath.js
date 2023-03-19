include "wwe.mm"
include "wa.mm"
include "cxp.mm"
include "wfr.mm"
include "wor.mm"
include "wefr.mm"
include "frxp.mm"
include "syl2an.mm"
include "weso.mm"
include "soxp.mm"
include "df-we.mm"
include "sylanbrc.mm"

theorem wexp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  assume wexp.1: |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ( R We A /\ S We B ) -> T We ( A X. B ) )

  proof
    cA
    cR
    wwe
    #
    cB
    cS
    wwe
    #
    wa
    cA
    cB
    cxp
    #
    cT
    wfr
    #
    @2
    cT
    wor
    #
    @2
    cT
    wwe
    @0
    cA
    cR
    wfr
    cB
    cS
    wfr
    @3
    @1
    cA
    cR
    wefr
    cB
    cS
    wefr
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    wexp.1
    frxp
    syl2an
    @0
    cA
    cR
    wor
    cB
    cS
    wor
    @4
    @1
    cA
    cR
    weso
    cB
    cS
    weso
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    wexp.1
    soxp
    syl2an
    @2
    cT
    df-we
    sylanbrc
end
