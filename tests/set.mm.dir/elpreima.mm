include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "cdm.mm"
include "cnvimass.mm"
include "sseli.mm"
include "fndm.mm"
include "eleq2d.mm"
include "syl5ib.mm"
include "wfun.mm"
include "fnfun.mm"
include "fvimacnvi.mm"
include "sylan.mm"
include "ex.mm"
include "jcad.mm"
include "wb.mm"
include "fvimacnv.mm"
include "funfni.mm"
include "biimpd.mm"
include "expimpd.mm"
include "impbid.mm"

theorem elpreima
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( F Fn A -> ( B e. ( `' F " C ) <-> ( B e. A /\ ( F ` B ) e. C ) ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cF
    ccnv
    cC
    cima
    #
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    cF
    cfv
    cC
    wcel
    #
    wa
    @0
    @2
    @3
    @4
    @2
    cB
    cF
    cdm
    #
    wcel
    @0
    @3
    @1
    @5
    cB
    cF
    cC
    cnvimass
    sseli
    @0
    @5
    cA
    cB
    cA
    cF
    fndm
    eleq2d
    syl5ib
    @0
    @2
    @4
    @0
    cF
    wfun
    @2
    @4
    cA
    cF
    fnfun
    cB
    cC
    cF
    fvimacnvi
    sylan
    ex
    jcad
    @0
    @3
    @4
    @2
    @0
    @3
    wa
    @4
    @2
    @4
    @2
    wb
    cA
    cB
    cF
    cB
    cC
    cF
    fvimacnv
    funfni
    biimpd
    expimpd
    impbid
end
