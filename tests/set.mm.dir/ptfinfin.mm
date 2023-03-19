include "cptfin.mm"
include "wcel.mm"
include "cv.mm"
include "crab.mm"
include "cfn.mm"
include "wral.mm"
include "wi.mm"
include "isptfin.mm"
include "ibi.mm"
include "wceq.mm"
include "eleq1.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "imp.mm"

theorem ptfinfin
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cX: class X
  let vp: setvar p
  assume ptfinfin.1: |- X = U. A

  disjoint A x
  disjoint P x
  disjoint X x
  disjoint p x
  disjoint A p
  disjoint P p
  disjoint X p
  assert |- ( ( A e. PtFin /\ P e. X ) -> { x e. A | P e. x } e. Fin )

  proof
    cA
    cptfin
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    vx
    cA
    crab
    #
    cfn
    wcel
    #
    @0
    vp
    cv
    #
    @2
    wcel
    #
    vx
    cA
    crab
    #
    cfn
    wcel
    #
    vp
    cX
    wral
    #
    @1
    @5
    wi
    @0
    @10
    vp
    vx
    cA
    cptfin
    cX
    ptfinfin.1
    isptfin
    ibi
    @9
    @5
    vp
    cP
    cX
    @6
    cP
    wceq
    #
    @8
    @4
    cfn
    @11
    @7
    @3
    vx
    cA
    @6
    cP
    @2
    eleq1
    rabbidv
    eleq1d
    rspccv
    syl
    imp
end
