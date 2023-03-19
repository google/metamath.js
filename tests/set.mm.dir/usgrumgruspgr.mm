include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cuspgr.mm"
include "wa.mm"
include "usgrumgr.mm"
include "usgruspgr.mm"
include "jca.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "cle.mm"
include "wbr.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "uspgrf.mm"
include "cedg.mm"
include "umgredgss.mm"
include "edgval.mm"
include "prprrab.mm"
include "eqcomi.mm"
include "3sstr3g.mm"
include "f1ssr.mm"
include "syl2anr.mm"
include "wb.mm"
include "isusgr.mm"
include "adantr.mm"
include "mpbird.mm"
include "impbii.mm"

theorem usgrumgruspgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph <-> ( G e. UMGraph /\ G e. USPGraph ) )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cumgr
    wcel
    #
    cG
    cuspgr
    wcel
    #
    wa
    #
    @0
    @1
    @2
    cG
    usgrumgr
    cG
    usgruspgr
    jca
    @3
    @0
    cG
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cG
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    cdif
    #
    crab
    #
    @4
    wf1
    #
    @2
    @5
    @6
    c2
    cle
    wbr
    vx
    @10
    crab
    #
    @4
    wf1
    @4
    crn
    #
    @11
    wss
    @12
    @1
    vx
    @4
    cG
    @8
    @8
    eqid
    #
    @4
    eqid
    #
    uspgrf
    @1
    cG
    cedg
    cfv
    @7
    vx
    @9
    crab
    #
    @14
    @11
    vx
    cG
    umgredgss
    cG
    edgval
    @11
    @17
    vx
    @8
    prprrab
    eqcomi
    3sstr3g
    @5
    @13
    @11
    @4
    f1ssr
    syl2anr
    @1
    @0
    @12
    wb
    @2
    vx
    cumgr
    @4
    cG
    @8
    @15
    @16
    isusgr
    adantr
    mpbird
    impbii
end
