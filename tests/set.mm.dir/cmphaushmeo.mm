include "ccmp.mm"
include "wcel.mm"
include "cha.mm"
include "ccn.mm"
include "co.mm"
include "w3a.mm"
include "chmeo.mm"
include "wf1o.mm"
include "hmeof1o.mm"
include "ccnv.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "ccld.mm"
include "cfv.mm"
include "wral.mm"
include "wi.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "syl.mm"
include "a1i.mm"
include "wrel.mm"
include "wceq.mm"
include "f1orel.mm"
include "ad2antll.mm"
include "dfrel2.mm"
include "sylib.mm"
include "imaeq1d.mm"
include "wss.mm"
include "crest.mm"
include "simp2.mm"
include "adantr.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseq.mm"
include "simpl3.mm"
include "simp1.mm"
include "simprl.mm"
include "cmpcld.mm"
include "syl2anc.mm"
include "imacmp.mm"
include "hauscmp.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "expr.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "ctopon.mm"
include "wb.mm"
include "ctop.mm"
include "haustop.mm"
include "toptopon.mm"
include "cmptop.mm"
include "iscncl.mm"
include "sylibrd.mm"
include "simp3.mm"
include "jctild.mm"
include "ishmeo.mm"
include "syl6ibr.mm"
include "impbid2.mm"

theorem cmphaushmeo
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vf: setvar f
  assume cmphaushmeo.1: |- X = U. J
  assume cmphaushmeo.2: |- Y = U. K


  assert |- ( ( J e. Comp /\ K e. Haus /\ F e. ( J Cn K ) ) -> ( F e. ( J Homeo K ) <-> F : X -1-1-onto-> Y ) )

  proof
    cJ
    ccmp
    wcel
    #
    cK
    cha
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    w3a
    #
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    cF
    cJ
    cK
    cX
    cY
    cmphaushmeo.1
    cmphaushmeo.2
    hmeof1o
    @3
    @5
    @2
    cF
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    #
    wa
    @4
    @3
    @5
    @7
    @2
    @3
    @5
    cY
    cX
    @6
    wf
    #
    @6
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cK
    ccld
    cfv
    #
    wcel
    #
    vx
    cJ
    ccld
    cfv
    #
    wral
    #
    wa
    #
    @7
    @3
    @5
    @8
    @15
    @5
    @8
    wi
    @3
    @5
    cY
    cX
    @6
    wf1o
    @8
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @6
    f1of
    syl
    a1i
    @3
    @5
    @13
    vx
    @14
    @3
    @10
    @14
    wcel
    #
    @5
    @13
    @3
    @17
    @5
    wa
    #
    wa
    #
    @11
    cF
    @10
    cima
    #
    @12
    @19
    @9
    cF
    @10
    @19
    cF
    wrel
    #
    @9
    cF
    wceq
    @5
    @21
    @3
    @17
    cX
    cY
    cF
    f1orel
    ad2antll
    cF
    dfrel2
    sylib
    imaeq1d
    @19
    @1
    @20
    cY
    wss
    cK
    @20
    crest
    co
    ccmp
    wcel
    #
    @20
    @12
    wcel
    @3
    @1
    @18
    @0
    @1
    @2
    simp2
    #
    adantr
    @19
    cF
    crn
    #
    @20
    cY
    cF
    @10
    imassrn
    @19
    cX
    cY
    cF
    wfo
    #
    @24
    cY
    wceq
    @5
    @25
    @3
    @17
    cX
    cY
    cF
    f1ofo
    ad2antll
    cX
    cY
    cF
    forn
    syl
    syl5sseq
    @19
    @2
    cJ
    @10
    crest
    co
    ccmp
    wcel
    #
    @22
    @0
    @1
    @2
    @18
    simpl3
    @19
    @0
    @17
    @26
    @3
    @0
    @18
    @0
    @1
    @2
    simp1
    #
    adantr
    @3
    @17
    @5
    simprl
    @10
    cJ
    cmpcld
    syl2anc
    @10
    cF
    cJ
    cK
    imacmp
    syl2anc
    @20
    cK
    cY
    cmphaushmeo.2
    hauscmp
    syl3anc
    eqeltrd
    expr
    ralrimdva
    jcad
    @3
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @7
    @16
    wb
    @3
    cK
    ctop
    wcel
    #
    @28
    @3
    @1
    @30
    @23
    cK
    haustop
    syl
    cK
    cY
    cmphaushmeo.2
    toptopon
    sylib
    @3
    cJ
    ctop
    wcel
    #
    @29
    @3
    @0
    @31
    @27
    cJ
    cmptop
    syl
    cJ
    cX
    cmphaushmeo.1
    toptopon
    sylib
    vx
    @6
    cK
    cJ
    cY
    cX
    iscncl
    syl2anc
    sylibrd
    @0
    @1
    @2
    simp3
    jctild
    cF
    cJ
    cK
    ishmeo
    syl6ibr
    impbid2
end
