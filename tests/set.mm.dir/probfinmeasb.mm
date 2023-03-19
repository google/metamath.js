include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "crp.mm"
include "wa.mm"
include "cxdiv.mm"
include "cofc.mm"
include "co.mm"
include "crn.mm"
include "cdm.mm"
include "c1.mm"
include "wceq.mm"
include "cprb.mm"
include "measdivcst.mm"
include "wfn.mm"
include "csiga.mm"
include "measfn.mm"
include "adantr.mm"
include "measbase.mm"
include "simpr.mm"
include "ofcfn.mm"
include "fndm.mm"
include "syl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "measbasedom.mm"
include "sylibr.mm"
include "unieqd.mm"
include "unielsiga.mm"
include "eqidd.mm"
include "ofcval.mm"
include "mpdan.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "rpre.mm"
include "rpne0.mm"
include "xdivid.mm"
include "syl2anc.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "elprob.mm"
include "sylanbrc.mm"

theorem probfinmeasb
  let cS: class S
  let cM: class M


  assert |- ( ( M e. ( measures ` S ) /\ ( M ` U. S ) e. RR+ ) -> ( M oFC /e ( M ` U. S ) ) e. Prob )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cS
    cuni
    #
    cM
    cfv
    #
    crp
    wcel
    #
    wa
    #
    cM
    @3
    cxdiv
    cofc
    co
    #
    cmeas
    crn
    cuni
    wcel
    #
    @6
    cdm
    #
    cuni
    #
    @6
    cfv
    #
    c1
    wceq
    @6
    cprb
    wcel
    @5
    @6
    @8
    cmeas
    cfv
    #
    wcel
    @7
    @5
    @6
    @0
    @11
    @3
    cS
    cM
    measdivcst
    @5
    @8
    cS
    cmeas
    @5
    @6
    cS
    wfn
    @8
    cS
    wceq
    @5
    cS
    @3
    cxdiv
    cM
    csiga
    crn
    cuni
    #
    crp
    @1
    cM
    cS
    wfn
    @4
    cS
    cM
    measfn
    adantr
    #
    @1
    cS
    @12
    wcel
    #
    @4
    cS
    cM
    measbase
    adantr
    #
    @1
    @4
    simpr
    #
    ofcfn
    cS
    @6
    fndm
    syl
    #
    fveq2d
    eleqtrrd
    @6
    measbasedom
    sylibr
    @5
    @10
    @2
    @6
    cfv
    #
    @3
    @3
    cxdiv
    co
    #
    c1
    @5
    @9
    @2
    @6
    @5
    @8
    cS
    @17
    unieqd
    fveq2d
    @5
    @2
    cS
    wcel
    #
    @18
    @19
    wceq
    @5
    @14
    @20
    @15
    cS
    unielsiga
    syl
    @5
    cS
    @3
    @3
    cxdiv
    cM
    @12
    crp
    @2
    @13
    @15
    @16
    @5
    @20
    wa
    @3
    eqidd
    ofcval
    mpdan
    @4
    @19
    c1
    wceq
    #
    @1
    @4
    @3
    cr
    wcel
    @3
    cc0
    wne
    @21
    @3
    rpre
    @3
    rpne0
    @3
    xdivid
    syl2anc
    adantl
    3eqtrd
    @6
    elprob
    sylanbrc
end
