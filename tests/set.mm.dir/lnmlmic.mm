include "clmic.mm"
include "wbr.mm"
include "cv.mm"
include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "clnm.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "brlmic.mm"
include "n0.mm"
include "bitri.mm"
include "wa.mm"
include "clmhm.mm"
include "crn.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "lmimlmhm.mm"
include "adantr.mm"
include "simpr.mm"
include "wf1o.mm"
include "wfo.mm"
include "eqid.mm"
include "lmimf1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "lnmepi.mm"
include "syl3anc.mm"
include "ccnv.mm"
include "islmim2.mm"
include "simprbi.mm"
include "cdm.mm"
include "dfdm4.mm"
include "f1odm.mm"
include "syl.mm"
include "syl5eqr.mm"
include "impbida.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem lnmlmic
  let cR: class R
  let cS: class S
  let va: setvar a


  assert |- ( R ~=m S -> ( R e. LNoeM <-> S e. LNoeM ) )

  proof
    cR
    cS
    clmic
    wbr
    #
    va
    cv
    #
    cR
    cS
    clmim
    co
    #
    wcel
    #
    va
    wex
    #
    cR
    clnm
    wcel
    #
    cS
    clnm
    wcel
    #
    wb
    #
    @0
    @2
    c0
    wne
    @4
    cR
    cS
    brlmic
    va
    @2
    n0
    bitri
    @3
    @7
    va
    @3
    @5
    @6
    @3
    @5
    wa
    @1
    cR
    cS
    clmhm
    co
    wcel
    #
    @5
    @1
    crn
    cS
    cbs
    cfv
    #
    wceq
    #
    @6
    @3
    @8
    @5
    cR
    cS
    @1
    lmimlmhm
    adantr
    @3
    @5
    simpr
    @3
    @10
    @5
    @3
    cR
    cbs
    cfv
    #
    @9
    @1
    wf1o
    #
    @11
    @9
    @1
    wfo
    @10
    @11
    @9
    cR
    cS
    @1
    @11
    eqid
    #
    @9
    eqid
    #
    lmimf1o
    #
    @11
    @9
    @1
    f1ofo
    @11
    @9
    @1
    forn
    3syl
    adantr
    @9
    cR
    cS
    @1
    @14
    lnmepi
    syl3anc
    @3
    @6
    wa
    #
    @1
    ccnv
    #
    cS
    cR
    clmhm
    co
    wcel
    #
    @6
    @17
    crn
    #
    @11
    wceq
    @5
    @3
    @18
    @6
    @3
    @8
    @18
    cR
    cS
    @1
    islmim2
    simprbi
    adantr
    @3
    @6
    simpr
    @16
    @19
    @1
    cdm
    #
    @11
    @1
    dfdm4
    @3
    @20
    @11
    wceq
    #
    @6
    @3
    @12
    @21
    @15
    @11
    @9
    @1
    f1odm
    syl
    adantr
    syl5eqr
    @11
    cS
    cR
    @17
    @13
    lnmepi
    syl3anc
    impbida
    exlimiv
    sylbi
end
