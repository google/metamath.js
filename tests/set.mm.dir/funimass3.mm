include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "ccnv.mm"
include "wcel.mm"
include "wral.mm"
include "cfv.mm"
include "funimass4.mm"
include "wb.mm"
include "ssel.mm"
include "fvimacnv.mm"
include "ex.mm"
include "syl9r.mm"
include "imp31.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "dfss3.mm"
include "syl6bbr.mm"

theorem funimass3
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( ( Fun F /\ A C_ dom F ) -> ( ( F " A ) C_ B <-> A C_ ( `' F " B ) ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    wa
    #
    cF
    cA
    cima
    cB
    wss
    #
    vx
    cv
    #
    cF
    ccnv
    cB
    cima
    #
    wcel
    #
    vx
    cA
    wral
    #
    cA
    @6
    wss
    @3
    @4
    @5
    cF
    cfv
    cB
    wcel
    #
    vx
    cA
    wral
    @8
    vx
    cA
    cB
    cF
    funimass4
    @3
    @9
    @7
    vx
    cA
    @0
    @2
    @5
    cA
    wcel
    #
    @9
    @7
    wb
    #
    @2
    @10
    @5
    @1
    wcel
    #
    @0
    @11
    cA
    @1
    @5
    ssel
    @0
    @12
    @11
    @5
    cB
    cF
    fvimacnv
    ex
    syl9r
    imp31
    ralbidva
    bitrd
    vx
    cA
    @6
    dfss3
    syl6bbr
end
