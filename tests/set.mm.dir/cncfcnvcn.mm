include "ccmp.mm"
include "wcel.mm"
include "ccncf.mm"
include "co.mm"
include "wa.mm"
include "crest.mm"
include "chmeo.mm"
include "ccnv.mm"
include "ccn.mm"
include "wf1o.mm"
include "wb.mm"
include "simpr.mm"
include "cc.mm"
include "wss.mm"
include "wceq.mm"
include "cncfrss.mm"
include "adantl.mm"
include "cncfrss2.mm"
include "eqid.mm"
include "cncfcn.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "ishmeo.mm"
include "baib.mm"
include "syl.mm"
include "cuni.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restuni.mm"
include "sylancr.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "cha.mm"
include "simpl.mm"
include "cvv.mm"
include "cnfldhaus.mm"
include "cnex.mm"
include "ssex.mm"
include "resthaus.mm"
include "cmphaushmeo.mm"
include "syl3anc.mm"
include "3bitr4d.mm"
include "eleq2d.mm"

theorem cncfcnvcn
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume cncfcnvcn.j: |- J = ( TopOpen ` CCfld )
  assume cncfcnvcn.k: |- K = ( J |`t X )


  assert |- ( ( K e. Comp /\ F e. ( X -cn-> Y ) ) -> ( F : X -1-1-onto-> Y <-> `' F e. ( Y -cn-> X ) ) )

  proof
    cK
    ccmp
    wcel
    #
    cF
    cX
    cY
    ccncf
    co
    #
    wcel
    #
    wa
    #
    cF
    cK
    cJ
    cY
    crest
    co
    #
    chmeo
    co
    wcel
    #
    cF
    ccnv
    #
    @4
    cK
    ccn
    co
    #
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    @6
    cY
    cX
    ccncf
    co
    #
    wcel
    @3
    cF
    cK
    @4
    ccn
    co
    #
    wcel
    #
    @5
    @8
    wb
    @3
    cF
    @1
    @11
    @0
    @2
    simpr
    @3
    cX
    cc
    wss
    #
    cY
    cc
    wss
    #
    @1
    @11
    wceq
    @2
    @13
    @0
    cX
    cY
    cF
    cncfrss
    adantl
    #
    @2
    @14
    @0
    cX
    cY
    cF
    cncfrss2
    adantl
    #
    cX
    cY
    cJ
    cK
    @4
    cncfcnvcn.j
    cncfcnvcn.k
    @4
    eqid
    #
    cncfcn
    syl2anc
    eleqtrd
    #
    @5
    @12
    @8
    cF
    cK
    @4
    ishmeo
    baib
    syl
    @3
    cX
    @4
    cuni
    #
    cF
    wf1o
    #
    cK
    cuni
    #
    @19
    cF
    wf1o
    #
    @9
    @5
    @3
    cX
    @21
    wceq
    @20
    @22
    wb
    @3
    cX
    cJ
    cX
    crest
    co
    #
    cuni
    #
    @21
    @3
    cJ
    ctop
    wcel
    #
    @13
    cX
    @24
    wceq
    cJ
    cncfcnvcn.j
    cnfldtop
    #
    @15
    cX
    cJ
    cc
    cc
    cJ
    cJ
    cncfcnvcn.j
    cnfldtopon
    toponunii
    #
    restuni
    sylancr
    cK
    @23
    cncfcnvcn.k
    unieqi
    syl6eqr
    cX
    @21
    @19
    cF
    f1oeq2
    syl
    @3
    cY
    @19
    wceq
    #
    @9
    @20
    wb
    @3
    @25
    @14
    @28
    @26
    @16
    cY
    cJ
    cc
    @27
    restuni
    sylancr
    cY
    @19
    cX
    cF
    f1oeq3
    syl
    @3
    @0
    @4
    cha
    wcel
    #
    @12
    @5
    @22
    wb
    @0
    @2
    simpl
    @3
    cJ
    cha
    wcel
    cY
    cvv
    wcel
    #
    @29
    cJ
    cncfcnvcn.j
    cnfldhaus
    @3
    @14
    @30
    @16
    cY
    cc
    cnex
    ssex
    syl
    cY
    cJ
    cvv
    resthaus
    sylancr
    @18
    cF
    cK
    @4
    @21
    @19
    @21
    eqid
    @19
    eqid
    cmphaushmeo
    syl3anc
    3bitr4d
    @3
    @10
    @7
    @6
    @3
    @14
    @13
    @10
    @7
    wceq
    @16
    @15
    cY
    cX
    cJ
    @4
    cK
    cncfcnvcn.j
    @17
    cncfcnvcn.k
    cncfcn
    syl2anc
    eleq2d
    3bitr4d
end
