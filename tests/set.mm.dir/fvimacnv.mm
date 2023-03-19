include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "csn.mm"
include "cop.mm"
include "funfvop.mm"
include "wb.mm"
include "cvv.mm"
include "fvex.mm"
include "opelcnvg.mm"
include "mpan.mm"
include "adantl.mm"
include "mpbird.mm"
include "elimasng.mm"
include "wss.mm"
include "snss.mm"
include "imass2.mm"
include "sylbi.mm"
include "sseld.mm"
include "syl5com.mm"
include "wi.mm"
include "fvimacnvi.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem fvimacnv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( Fun F /\ A e. dom F ) -> ( ( F ` A ) e. B <-> A e. ( `' F " B ) ) )

  proof
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cB
    wcel
    #
    cA
    cF
    ccnv
    #
    cB
    cima
    #
    wcel
    #
    @3
    cA
    @6
    @4
    csn
    #
    cima
    #
    wcel
    #
    @5
    @8
    @3
    @11
    @4
    cA
    cop
    @6
    wcel
    #
    @3
    @12
    cA
    @4
    cop
    cF
    wcel
    #
    cA
    cF
    funfvop
    @2
    @12
    @13
    wb
    #
    @0
    @4
    cvv
    wcel
    #
    @2
    @14
    cA
    cF
    fvex
    #
    @4
    cA
    cvv
    @1
    cF
    opelcnvg
    mpan
    adantl
    mpbird
    @2
    @11
    @12
    wb
    #
    @0
    @15
    @2
    @17
    @16
    @6
    @4
    cA
    cvv
    @1
    elimasng
    mpan
    adantl
    mpbird
    @5
    @10
    @7
    cA
    @5
    @9
    cB
    wss
    @10
    @7
    wss
    @4
    cB
    @16
    snss
    @9
    cB
    @6
    imass2
    sylbi
    sseld
    syl5com
    @0
    @8
    @5
    wi
    @2
    @0
    @8
    @5
    cA
    cB
    cF
    fvimacnvi
    ex
    adantr
    impbid
end
