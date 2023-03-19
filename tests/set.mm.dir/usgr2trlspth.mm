include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "ctrls.mm"
include "wbr.mm"
include "cspths.mm"
include "cc0.mm"
include "wne.mm"
include "usgr2trlncl.mm"
include "imp.mm"
include "wi.mm"
include "cwlks.mm"
include "cwlkson.mm"
include "co.mm"
include "trliswlk.mm"
include "wlkonwlk.mm"
include "cspthson.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "neeq2d.mm"
include "biimpd.mm"
include "adantl.mm"
include "usgr2wlkspth.mm"
include "syl3anc.mm"
include "spthonisspth.mm"
include "syl6bi.mm"
include "expcom.mm"
include "com13.mm"
include "3syl.mm"
include "impcom.mm"
include "mpd.mm"
include "ex.mm"
include "cpths.mm"
include "spthispth.mm"
include "pthistrl.mm"
include "syl.mm"
include "impbid1.mm"

theorem usgr2trlspth
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( G e. USGraph /\ ( # ` F ) = 2 ) -> ( F ( Trails ` G ) P <-> F ( SPaths ` G ) P ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    @3
    @4
    @5
    @3
    @4
    wa
    cc0
    cP
    cfv
    #
    c2
    cP
    cfv
    #
    wne
    #
    @5
    @3
    @4
    @8
    cP
    cF
    cG
    usgr2trlncl
    imp
    @4
    @3
    @8
    @5
    wi
    #
    @4
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cP
    @6
    @1
    cP
    cfv
    #
    cG
    cwlkson
    cfv
    co
    wbr
    #
    @3
    @9
    wi
    cP
    cF
    cG
    trliswlk
    cP
    cF
    cG
    wlkonwlk
    @8
    @3
    @11
    @5
    @3
    @8
    @11
    @5
    wi
    @3
    @8
    wa
    #
    @11
    cF
    cP
    @6
    @10
    cG
    cspthson
    cfv
    co
    wbr
    #
    @5
    @12
    @0
    @2
    @6
    @10
    wne
    #
    @11
    @13
    wb
    @0
    @2
    @8
    simpll
    @0
    @2
    @8
    simplr
    @3
    @8
    @14
    @2
    @8
    @14
    wi
    @0
    @2
    @8
    @14
    @2
    @7
    @10
    @6
    @2
    @10
    @7
    @1
    c2
    cP
    fveq2
    eqcomd
    neeq2d
    biimpd
    adantl
    imp
    @6
    @10
    cP
    cF
    cG
    usgr2wlkspth
    syl3anc
    @6
    @10
    cP
    cF
    cG
    spthonisspth
    syl6bi
    expcom
    com13
    3syl
    impcom
    mpd
    ex
    @5
    cF
    cP
    cG
    cpths
    cfv
    wbr
    @4
    cP
    cF
    cG
    spthispth
    cP
    cF
    cG
    pthistrl
    syl
    impbid1
end
