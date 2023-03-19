include "cnrg.mm"
include "wcel.mm"
include "cdr.mm"
include "wa.mm"
include "ctrg.mm"
include "cmgp.mm"
include "cfv.mm"
include "cui.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "ctdrg.mm"
include "nrgtrg.mm"
include "adantr.mm"
include "simpr.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cinvr.mm"
include "ctopn.mm"
include "crest.mm"
include "ccn.mm"
include "crg.mm"
include "nrgring.mm"
include "eqid.mm"
include "unitgrp.mm"
include "syl.mm"
include "csubmnd.mm"
include "trgtmd.mm"
include "unitsubm.mm"
include "submtmd.mm"
include "syl2anc.mm"
include "cbs.mm"
include "nrginvrcn.mm"
include "mgptopn.mm"
include "resstopn.mm"
include "invrfval.mm"
include "istgp.mm"
include "syl3anbrc.mm"
include "istdrg.mm"

theorem nrgtdrg
  let cR: class R


  assert |- ( ( R e. NrmRing /\ R e. DivRing ) -> R e. TopDRing )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cdr
    wcel
    #
    wa
    #
    cR
    ctrg
    wcel
    #
    @1
    cR
    cmgp
    cfv
    #
    cR
    cui
    cfv
    #
    cress
    co
    #
    ctgp
    wcel
    #
    cR
    ctdrg
    wcel
    @0
    @3
    @1
    cR
    nrgtrg
    adantr
    #
    @0
    @1
    simpr
    @2
    @6
    cgrp
    wcel
    #
    @6
    ctmd
    wcel
    #
    cR
    cinvr
    cfv
    #
    cR
    ctopn
    cfv
    #
    @5
    crest
    co
    #
    @13
    ccn
    co
    wcel
    #
    @7
    @2
    cR
    crg
    wcel
    #
    @9
    @0
    @15
    @1
    cR
    nrgring
    adantr
    #
    cR
    @5
    @6
    @5
    eqid
    #
    @6
    eqid
    #
    unitgrp
    syl
    @2
    @4
    ctmd
    wcel
    #
    @5
    @4
    csubmnd
    cfv
    wcel
    #
    @10
    @2
    @3
    @19
    @8
    cR
    @4
    @4
    eqid
    #
    trgtmd
    syl
    @2
    @15
    @20
    @16
    cR
    @5
    @4
    @17
    @21
    unitsubm
    syl
    @5
    @4
    @6
    @18
    submtmd
    syl2anc
    @0
    @14
    @1
    cR
    @5
    @11
    @12
    cR
    cbs
    cfv
    #
    @22
    eqid
    @17
    @11
    eqid
    #
    @12
    eqid
    #
    nrginvrcn
    adantr
    @6
    @11
    @13
    @5
    @6
    @12
    @4
    @18
    cR
    @12
    @4
    @21
    @24
    mgptopn
    resstopn
    cR
    @5
    @6
    @11
    @17
    @18
    @23
    invrfval
    istgp
    syl3anbrc
    cR
    @5
    @4
    @21
    @17
    istdrg
    syl3anbrc
end
