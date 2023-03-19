include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wss.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "crn.mm"
include "wrex.mm"
include "wlkvtxeledg.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "fvex.mm"
include "prnz.mm"
include "ssn0.mm"
include "mpan2.mm"
include "adantl.mm"
include "fvn0fvelrn.mm"
include "syl.mm"
include "wceq.mm"
include "wb.mm"
include "sseq2.mm"
include "simpr.mm"
include "rspcedvd.mm"
include "ex.mm"
include "ralimdva.mm"
include "mpd.mm"

theorem wlkvtxiedg
  let cP: class P
  let ve: setvar e
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  assume wlkvtxeledg.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  disjoint F e
  disjoint G e
  disjoint I e
  disjoint I k
  disjoint e k
  disjoint P e
  assert |- ( F ( Walks ` G ) P -> A. k e. ( 0 ..^ ( # ` F ) ) E. e e. ran I { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ e )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    vk
    cv
    #
    cP
    cfv
    #
    @1
    c1
    caddc
    co
    cP
    cfv
    #
    cpr
    #
    @1
    cF
    cfv
    #
    cI
    cfv
    #
    wss
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    @4
    ve
    cv
    #
    wss
    #
    ve
    cI
    crn
    #
    wrex
    #
    vk
    @8
    wral
    cP
    vk
    cF
    cG
    cI
    wlkvtxeledg.i
    wlkvtxeledg
    @0
    @7
    @12
    vk
    @8
    @0
    @1
    @8
    wcel
    wa
    #
    @7
    @12
    @13
    @7
    wa
    #
    @10
    @7
    ve
    @6
    @11
    @14
    @6
    c0
    wne
    #
    @6
    @11
    wcel
    @7
    @15
    @13
    @7
    @4
    c0
    wne
    @15
    @2
    @3
    @1
    cP
    fvex
    prnz
    @4
    @6
    ssn0
    mpan2
    adantl
    cI
    @5
    fvn0fvelrn
    syl
    @9
    @6
    wceq
    @10
    @7
    wb
    @14
    @9
    @6
    @4
    sseq2
    adantl
    @13
    @7
    simpr
    rspcedvd
    ex
    ralimdva
    mpd
end
