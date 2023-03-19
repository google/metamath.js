include "cxp.mm"
include "ccnv.mm"
include "wf1o.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "wrel.mm"
include "relxp.mm"
include "cnvf1o.mm"
include "ax-mp.mm"
include "wceq.mm"
include "wb.mm"
include "f1oeq1.mm"
include "mpbir.mm"
include "cnvxp.mm"
include "f1oeq3.mm"
include "mpbi.mm"

theorem xpcomf1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cG: class G
  assume xpcomf1o.1: |- F = ( x e. ( A X. B ) |-> U. `' { x } )

  disjoint A x
  disjoint B x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G v
  disjoint G w
  assert |- F : ( A X. B ) -1-1-onto-> ( B X. A )

  proof
    cA
    cB
    cxp
    #
    @0
    ccnv
    #
    cF
    wf1o
    #
    @0
    cB
    cA
    cxp
    #
    cF
    wf1o
    #
    @2
    @0
    @1
    vx
    @0
    vx
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    wf1o
    #
    @0
    wrel
    @6
    cA
    cB
    relxp
    vx
    @0
    cnvf1o
    ax-mp
    cF
    @5
    wceq
    @2
    @6
    wb
    xpcomf1o.1
    @0
    @1
    cF
    @5
    f1oeq1
    ax-mp
    mpbir
    @1
    @3
    wceq
    @2
    @4
    wb
    cA
    cB
    cnvxp
    @1
    @3
    @0
    cF
    f1oeq3
    ax-mp
    mpbi
end
