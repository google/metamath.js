include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "clinco.mm"
include "co.mm"
include "cbs.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "cpw.mm"
include "wb.mm"
include "simp1.mm"
include "eqid.mm"
include "lssss.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "sstr.mm"
include "cvv.mm"
include "fvex.mm"
include "ssex.mm"
include "elpwg.mm"
include "biimprd.mm"
include "mpcom.mm"
include "syl.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "lcoval.mm"
include "syl2anc.mm"
include "lincellss.mm"
include "imp.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "expd.mm"
include "com12.mm"
include "adantr.mm"
include "com13.mm"
include "impr.mm"
include "rexlimiva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem ellcoellss
  let vx: setvar x
  let cS: class S
  let cM: class M
  let cV: class V
  let vf: setvar f
  let vk: setvar k

  disjoint M x
  disjoint S x
  disjoint V x
  disjoint M f
  disjoint f x
  disjoint S f
  disjoint V f
  disjoint k x
  assert |- ( ( M e. LMod /\ S e. ( LSubSp ` M ) /\ V C_ S ) -> A. x e. ( M LinCo V ) x e. S )

  proof
    cM
    clmod
    wcel
    #
    cS
    cM
    clss
    cfv
    #
    wcel
    #
    cV
    cS
    wss
    #
    w3a
    #
    vx
    cv
    #
    cS
    wcel
    #
    vx
    cM
    cV
    clinco
    co
    #
    @4
    @5
    @7
    wcel
    #
    @5
    cM
    cbs
    cfv
    #
    wcel
    #
    vf
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    cfsupp
    wbr
    #
    @5
    @11
    cV
    cM
    clinc
    cfv
    co
    #
    wceq
    #
    wa
    #
    vf
    @12
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wrex
    #
    wa
    #
    @6
    @4
    @0
    cV
    @9
    cpw
    wcel
    #
    @8
    @20
    wb
    @0
    @2
    @3
    simp1
    @4
    cS
    @9
    wss
    #
    @21
    @2
    @0
    @22
    @3
    @1
    cS
    @9
    cM
    @9
    eqid
    #
    @1
    eqid
    lssss
    3ad2ant2
    @3
    @0
    @22
    @21
    wi
    @2
    @3
    @22
    @21
    @3
    @22
    wa
    cV
    @9
    wss
    #
    @21
    cV
    cS
    @9
    sstr
    cV
    cvv
    wcel
    #
    @24
    @21
    cV
    @9
    cM
    cbs
    fvex
    ssex
    @25
    @21
    @24
    cV
    @9
    cvv
    elpwg
    biimprd
    mpcom
    syl
    ex
    3ad2ant3
    mpd
    @9
    @5
    @17
    @12
    cM
    cV
    clmod
    vf
    @23
    @12
    eqid
    @17
    eqid
    lcoval
    syl2anc
    @4
    @10
    @19
    @6
    @19
    @4
    @10
    wa
    #
    @6
    @16
    @26
    @6
    wi
    #
    vf
    @18
    @11
    @18
    wcel
    #
    @13
    @15
    @27
    @26
    @15
    @28
    @13
    wa
    #
    @6
    @4
    @15
    @29
    @6
    wi
    #
    wi
    @10
    @15
    @4
    @30
    @15
    @4
    @29
    @6
    @4
    @29
    wa
    @6
    @15
    @14
    cS
    wcel
    #
    @4
    @29
    @31
    cS
    @11
    cM
    cV
    lincellss
    imp
    @5
    @14
    cS
    eleq1
    syl5ibr
    expd
    com12
    adantr
    com13
    impr
    rexlimiva
    com12
    expimpd
    sylbid
    ralrimiv
end
