include "ctop.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "crest.mm"
include "cxko.mm"
include "cv.mm"
include "cmpt.mm"
include "cuni.mm"
include "ctopon.mm"
include "wss.mm"
include "eqid.mm"
include "xkotopon.mm"
include "3adant3.mm"
include "wceq.mm"
include "wf.mm"
include "topopn.mm"
include "3ad2ant1.mm"
include "fconst6g.mm"
include "3ad2ant2.mm"
include "pttop.mm"
include "syl2anc.mm"
include "cmap.mm"
include "cnf.mm"
include "cvv.mm"
include "uniexg.mm"
include "elmapd.mm"
include "syl5ibr.mm"
include "ssrdv.mm"
include "simp2.mm"
include "ptuniconst.mm"
include "sseqtrd.mm"
include "restuni.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "xkoptsub.mm"
include "cnss1.mm"
include "cres.mm"
include "resmptd.mm"
include "simp3.mm"
include "ptpjcn.mm"
include "syl3anc.mm"
include "fvconst2g.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "cnrest.mm"
include "eqeltrrd.mm"
include "sseldd.mm"

theorem xkopjcn
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cX: class X
  assume xkopjcn.1: |- X = U. R

  disjoint A f
  disjoint R f
  disjoint S f
  disjoint X f
  assert |- ( ( R e. Top /\ S e. Top /\ A e. X ) -> ( f e. ( R Cn S ) |-> ( f ` A ) ) e. ( ( S ^ko R ) Cn S ) )

  proof
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cX
    cS
    csn
    cxp
    #
    cpt
    cfv
    #
    cR
    cS
    ccn
    co
    #
    crest
    co
    #
    cS
    ccn
    co
    #
    cS
    cR
    cxko
    co
    #
    cS
    ccn
    co
    #
    vf
    @6
    cA
    vf
    cv
    #
    cfv
    #
    cmpt
    #
    @3
    @9
    @7
    cuni
    #
    ctopon
    cfv
    #
    wcel
    @7
    @9
    wss
    #
    @8
    @10
    wss
    @3
    @9
    @6
    ctopon
    cfv
    #
    @15
    @0
    @1
    @9
    @17
    wcel
    @2
    cR
    cS
    @9
    @9
    eqid
    xkotopon
    3adant3
    @3
    @6
    @14
    ctopon
    @3
    @5
    ctop
    wcel
    #
    @6
    @5
    cuni
    #
    wss
    #
    @6
    @14
    wceq
    @3
    cX
    cR
    wcel
    #
    cX
    ctop
    @4
    wf
    #
    @18
    @0
    @1
    @21
    @2
    cR
    cX
    xkopjcn.1
    topopn
    3ad2ant1
    #
    @1
    @0
    @22
    @2
    cX
    cS
    ctop
    fconst6g
    3ad2ant2
    #
    cX
    @4
    cR
    pttop
    syl2anc
    @3
    @6
    cS
    cuni
    #
    cX
    cmap
    co
    #
    @19
    @3
    vf
    @6
    @26
    @11
    @6
    wcel
    @11
    @26
    wcel
    @3
    cX
    @25
    @11
    wf
    @11
    cR
    cS
    cX
    @25
    xkopjcn.1
    @25
    eqid
    #
    cnf
    @3
    @25
    cX
    @11
    cvv
    cR
    @1
    @0
    @25
    cvv
    wcel
    @2
    cS
    ctop
    uniexg
    3ad2ant2
    @23
    elmapd
    syl5ibr
    ssrdv
    @3
    @21
    @1
    @26
    @19
    wceq
    @23
    @0
    @1
    @2
    simp2
    cX
    cS
    @5
    cR
    @25
    @5
    eqid
    #
    @27
    ptuniconst
    syl2anc
    sseqtrd
    #
    @6
    @5
    @19
    @19
    eqid
    #
    restuni
    syl2anc
    fveq2d
    eleqtrd
    @0
    @1
    @16
    @2
    cR
    cS
    @5
    cX
    xkopjcn.1
    @28
    xkoptsub
    3adant3
    @7
    @9
    cS
    @14
    @14
    eqid
    cnss1
    syl2anc
    @3
    vf
    @19
    @12
    cmpt
    #
    @6
    cres
    #
    @13
    @8
    @3
    vf
    @19
    @6
    @12
    @29
    resmptd
    @3
    @31
    @5
    cS
    ccn
    co
    #
    wcel
    @20
    @32
    @8
    wcel
    @3
    @31
    @5
    cA
    @4
    cfv
    #
    ccn
    co
    #
    @33
    @3
    @21
    @22
    @2
    @31
    @35
    wcel
    @23
    @24
    @0
    @1
    @2
    simp3
    vf
    cX
    @4
    cA
    @5
    cR
    @19
    @30
    @28
    ptpjcn
    syl3anc
    @3
    @34
    cS
    @5
    ccn
    @1
    @2
    @34
    cS
    wceq
    @0
    cX
    cS
    cA
    ctop
    fvconst2g
    3adant1
    oveq2d
    eleqtrd
    @29
    @6
    @31
    @5
    cS
    @19
    @30
    cnrest
    syl2anc
    eqeltrrd
    sseldd
end
