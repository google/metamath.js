include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "cfi.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "elin.mm"
include "elpwi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "fbssint.mm"
include "3expb.mm"
include "sylan2.mm"
include "0nelfb.mm"
include "ad2antrr.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "adantl.mm"
include "mtod.mm"
include "ss0.mm"
include "nsyl.mm"
include "adantrr.mm"
include "sseq2.mm"
include "biimprcd.mm"
include "ad2antll.mm"
include "rexlimddv.mm"
include "nrexdv.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "elfi.mm"
include "mpan.mm"
include "mtbird.mm"

theorem fbasfip
  let cF: class F
  let cX: class X
  let vy: setvar y
  let vz: setvar z


  assert |- ( F e. ( fBas ` X ) -> -. (/) e. ( fi ` F ) )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    c0
    cF
    cfi
    cfv
    wcel
    #
    c0
    vy
    cv
    #
    cint
    #
    wceq
    #
    vy
    cF
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @1
    @5
    vy
    @7
    @1
    @3
    @7
    wcel
    #
    wa
    #
    vz
    cv
    #
    @4
    wss
    #
    @5
    wn
    vz
    cF
    @9
    @1
    @3
    cF
    wss
    #
    @3
    cfn
    wcel
    #
    wa
    #
    @12
    vz
    cF
    wrex
    #
    @9
    @3
    @6
    wcel
    #
    @14
    wa
    @15
    @3
    @6
    cfn
    elin
    @17
    @13
    @14
    @3
    cF
    elpwi
    anim1i
    sylbi
    @1
    @13
    @14
    @16
    vz
    @3
    cX
    cF
    fbssint
    3expb
    sylan2
    @10
    @11
    cF
    wcel
    #
    @12
    wa
    wa
    @5
    @11
    c0
    wss
    #
    @10
    @18
    @19
    wn
    @12
    @10
    @18
    wa
    #
    @11
    c0
    wceq
    #
    @19
    @20
    @21
    c0
    cF
    wcel
    #
    @1
    @22
    wn
    @9
    @18
    cX
    cF
    0nelfb
    ad2antrr
    @18
    @21
    @22
    wi
    @10
    @21
    @18
    @22
    @11
    c0
    cF
    eleq1
    biimpcd
    adantl
    mtod
    @11
    ss0
    nsyl
    adantrr
    @12
    @5
    @19
    wi
    @10
    @18
    @5
    @19
    @12
    c0
    @4
    @11
    sseq2
    biimprcd
    ad2antll
    mtod
    rexlimddv
    nrexdv
    c0
    cvv
    wcel
    @1
    @2
    @8
    wb
    0ex
    vy
    c0
    cF
    cvv
    @0
    elfi
    mpan
    mtbird
end
