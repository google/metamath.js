include "cuspgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cushgr.mm"
include "wa.mm"
include "uspgrupgr.mm"
include "uspgrushgr.mm"
include "jca.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf1.mm"
include "crn.mm"
include "wss.mm"
include "eqid.mm"
include "ushgrf.mm"
include "cedg.mm"
include "edgval.mm"
include "upgredgss.mm"
include "syl5eqssr.mm"
include "f1ssr.mm"
include "syl2anr.mm"
include "wb.mm"
include "isuspgr.mm"
include "adantr.mm"
include "mpbird.mm"
include "impbii.mm"

theorem uspgrupgrushgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USPGraph <-> ( G e. UPGraph /\ G e. USHGraph ) )

  proof
    cG
    cuspgr
    wcel
    #
    cG
    cupgr
    wcel
    #
    cG
    cushgr
    wcel
    #
    wa
    #
    @0
    @1
    @2
    cG
    uspgrupgr
    cG
    uspgrushgr
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
    c2
    cle
    wbr
    vx
    cG
    cvtx
    cfv
    #
    cpw
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
    @7
    @4
    wf1
    @4
    crn
    #
    @8
    wss
    @9
    @1
    @4
    cG
    @6
    @6
    eqid
    #
    @4
    eqid
    #
    ushgrf
    @1
    @10
    cG
    cedg
    cfv
    @8
    cG
    edgval
    vx
    cG
    upgredgss
    syl5eqssr
    @5
    @7
    @8
    @4
    f1ssr
    syl2anr
    @1
    @0
    @9
    wb
    @2
    vx
    cupgr
    @4
    cG
    @6
    @11
    @12
    isuspgr
    adantr
    mpbird
    impbii
end
