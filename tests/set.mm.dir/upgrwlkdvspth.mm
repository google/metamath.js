include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "w3a.mm"
include "cspths.mm"
include "wa.mm"
include "3simpc.mm"
include "cv.mm"
include "copab.mm"
include "wceq.mm"
include "upgrspthswlk.mm"
include "3ad2ant1.mm"
include "breqd.mm"
include "cvv.mm"
include "wb.mm"
include "wlkv.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "breq12.mm"
include "cnveq.mm"
include "funeqd.mm"
include "adantl.mm"
include "anbi12d.mm"
include "eqid.mm"
include "brabga.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem upgrwlkdvspth
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vf: setvar f
  let vp: setvar p


  assert |- ( ( G e. UPGraph /\ F ( Walks ` G ) P /\ Fun `' P ) -> F ( SPaths ` G ) P )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    #
    cP
    ccnv
    #
    wfun
    #
    w3a
    #
    cF
    cP
    cG
    cspths
    cfv
    #
    wbr
    #
    @2
    @4
    wa
    #
    @0
    @2
    @4
    3simpc
    @5
    @7
    cF
    cP
    vf
    cv
    #
    vp
    cv
    #
    @1
    wbr
    #
    @10
    ccnv
    #
    wfun
    #
    wa
    #
    vf
    vp
    copab
    #
    wbr
    #
    @8
    @5
    @6
    @15
    cF
    cP
    @0
    @2
    @6
    @15
    wceq
    @4
    vf
    cG
    vp
    upgrspthswlk
    3ad2ant1
    breqd
    @5
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    wa
    #
    @16
    @8
    wb
    @2
    @0
    @19
    @4
    @2
    cG
    cvv
    wcel
    #
    @17
    @18
    w3a
    @19
    cP
    cF
    cG
    wlkv
    @20
    @17
    @18
    3simpc
    syl
    3ad2ant2
    @14
    @8
    vf
    vp
    cF
    cP
    @15
    cvv
    cvv
    @9
    cF
    wceq
    #
    @10
    cP
    wceq
    #
    wa
    @11
    @2
    @13
    @4
    @9
    cF
    @10
    cP
    @1
    breq12
    @22
    @13
    @4
    wb
    @21
    @22
    @12
    @3
    @10
    cP
    cnveq
    funeqd
    adantl
    anbi12d
    @15
    eqid
    brabga
    syl
    bitrd
    mpbird
end
