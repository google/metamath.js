include "cnrg.mm"
include "wcel.mm"
include "ctgp.mm"
include "crg.mm"
include "cmgp.mm"
include "cfv.mm"
include "ctmd.mm"
include "ctrg.mm"
include "nrgtgp.mm"
include "nrgring.mm"
include "cmnd.mm"
include "ctps.mm"
include "cplusf.mm"
include "ctopn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "eqid.mm"
include "ringmgp.mm"
include "syl.mm"
include "cbs.mm"
include "ctopon.mm"
include "tgptps.mm"
include "istps.mm"
include "sylib.mm"
include "mgpbas.mm"
include "mgptopn.mm"
include "sylibr.mm"
include "crglmod.mm"
include "cnlm.mm"
include "rlmnlm.mm"
include "cid.mm"
include "rlmsca2.mm"
include "rlmscaf.mm"
include "rlmtopn.mm"
include "wceq.mm"
include "wtru.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "a1i.mm"
include "cts.mm"
include "c9.mm"
include "df-tset.mm"
include "topnpropd.mm"
include "trud.mm"
include "nlmvscn.mm"
include "istmd.mm"
include "syl3anbrc.mm"
include "istrg.mm"

theorem nrgtrg
  let cR: class R


  assert |- ( R e. NrmRing -> R e. TopRing )

  proof
    cR
    cnrg
    wcel
    #
    cR
    ctgp
    wcel
    #
    cR
    crg
    wcel
    #
    cR
    cmgp
    cfv
    #
    ctmd
    wcel
    #
    cR
    ctrg
    wcel
    cR
    nrgtgp
    #
    cR
    nrgring
    #
    @0
    @3
    cmnd
    wcel
    #
    @3
    ctps
    wcel
    #
    @3
    cplusf
    cfv
    #
    cR
    ctopn
    cfv
    #
    @10
    ctx
    co
    @10
    ccn
    co
    wcel
    #
    @4
    @0
    @2
    @7
    @6
    cR
    @3
    @3
    eqid
    #
    ringmgp
    syl
    @0
    @10
    cR
    cbs
    cfv
    #
    ctopon
    cfv
    wcel
    #
    @8
    @0
    cR
    ctps
    wcel
    #
    @14
    @0
    @1
    @15
    @5
    cR
    tgptps
    syl
    @13
    @10
    cR
    @13
    eqid
    #
    @10
    eqid
    #
    istps
    sylib
    @13
    @10
    @3
    @13
    cR
    @3
    @12
    @16
    mgpbas
    cR
    @10
    @3
    @12
    @17
    mgptopn
    #
    istps
    sylibr
    @0
    cR
    crglmod
    cfv
    #
    cnlm
    wcel
    @11
    cR
    rlmnlm
    @9
    cR
    cid
    cfv
    #
    @10
    @10
    @19
    cR
    rlmsca2
    cR
    rlmscaf
    cR
    rlmtopn
    @10
    @20
    ctopn
    cfv
    wceq
    wtru
    cR
    @20
    @13
    @20
    cbs
    cfv
    wceq
    wtru
    cR
    cbs
    c1
    @13
    df-base
    @16
    strfvi
    a1i
    cR
    cts
    cfv
    #
    @20
    cts
    cfv
    wceq
    wtru
    cR
    cts
    c9
    @21
    df-tset
    @21
    eqid
    strfvi
    a1i
    topnpropd
    trud
    nlmvscn
    syl
    @9
    @3
    @10
    @9
    eqid
    @18
    istmd
    syl3anbrc
    cR
    @3
    @12
    istrg
    syl3anbrc
end
