include "wf1o.mm"
include "wwe.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "breq2d.mm"
include "brabg.mm"
include "rgen2a.mm"
include "wa.mm"
include "wiso.mm"
include "df-isom.mm"
include "isowe.mm"
include "sylbir.mm"
include "mpan2.mm"
include "biimprd.mm"

theorem f1owe
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  assume f1owe.1: |- R = { <. x , y >. | ( F ` x ) S ( F ` y ) }

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint w z
  disjoint R z
  disjoint R w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint S z
  disjoint S w
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint F z
  disjoint F w
  assert |- ( F : A -1-1-onto-> B -> ( S We B -> R We A ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cA
    cR
    wwe
    #
    cB
    cS
    wwe
    #
    @0
    vz
    cv
    #
    vw
    cv
    #
    cR
    wbr
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vw
    cA
    wral
    vz
    cA
    wral
    #
    @1
    @2
    wb
    #
    @8
    vz
    vw
    cA
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cS
    wbr
    @5
    @14
    cS
    wbr
    @7
    vx
    vy
    @3
    @4
    cA
    cA
    cR
    vx
    vz
    weq
    @12
    @5
    @14
    cS
    @11
    @3
    cF
    fveq2
    breq1d
    vy
    vw
    weq
    @14
    @6
    @5
    cS
    @13
    @4
    cF
    fveq2
    breq2d
    f1owe.1
    brabg
    rgen2a
    @0
    @9
    wa
    cA
    cB
    cR
    cS
    cF
    wiso
    @10
    vz
    vw
    cA
    cB
    cR
    cS
    cF
    df-isom
    cA
    cB
    cR
    cS
    cF
    isowe
    sylbir
    mpan2
    biimprd
end
