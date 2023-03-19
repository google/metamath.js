include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "wb.mm"
include "c0.mm"
include "cpr.mm"
include "wceq.mm"
include "wi.mm"
include "topdifinffin.mm"
include "topdifinfindis.mm"
include "indistopon.mm"
include "eqeltrd.mm"
include "impbii.mm"
include "syl.mm"
include "pm3.2i.mm"

theorem topdifinf
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vy: setvar y
  assume topdifinf.t: |- T = { x e. ~P A | ( -. ( A \ x ) e. Fin \/ ( x = (/) \/ x = A ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint T y
  assert |- ( ( T e. ( TopOn ` A ) <-> A e. Fin ) /\ ( T e. ( TopOn ` A ) -> T = { (/) , A } ) )

  proof
    cT
    cA
    ctopon
    cfv
    #
    wcel
    #
    cA
    cfn
    wcel
    #
    wb
    @1
    cT
    c0
    cA
    cpr
    #
    wceq
    #
    wi
    @1
    @2
    vx
    cA
    cT
    topdifinf.t
    topdifinffin
    #
    @2
    cT
    @3
    @0
    vx
    cA
    cT
    topdifinf.t
    topdifinfindis
    #
    cA
    cfn
    indistopon
    eqeltrd
    impbii
    @1
    @2
    @4
    @5
    @6
    syl
    pm3.2i
end
