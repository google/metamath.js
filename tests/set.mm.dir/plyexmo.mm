include "cc.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cply.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wmo.mm"
include "wi.mm"
include "wal.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "c0p.mm"
include "ccnv.mm"
include "cima.mm"
include "simplr.mm"
include "simpll.mm"
include "sseld.mm"
include "wfn.mm"
include "cvv.mm"
include "wf.mm"
include "simprll.mm"
include "plyf.mm"
include "syl.mm"
include "ffn.mm"
include "adantr.mm"
include "simprrl.mm"
include "cnex.mm"
include "a1i.mm"
include "sselda.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "ffvelrnd.mm"
include "simprlr.mm"
include "simprrr.mm"
include "eqtr4d.mm"
include "fveq1d.mm"
include "fvres.mm"
include "adantl.mm"
include "3eqtr3d.mm"
include "subeq0bd.mm"
include "eqtrd.mm"
include "ex.mm"
include "jcad.mm"
include "wb.mm"
include "plysubcl.mm"
include "syl2anc.mm"
include "fniniseg.mm"
include "4syl.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "expcom.mm"
include "mtod.mm"
include "chash.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "eqid.mm"
include "fta1.mm"
include "syl2an.mm"
include "simpld.mm"
include "mt3d.mm"
include "df-0p.mm"
include "syl6eq.mm"
include "ofsubeq0.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "mo4.mm"
include "sylibr.mm"
include "plyssc.mm"
include "sseli.mm"
include "anim1i.mm"
include "moimi.mm"

theorem plyexmo
  let cD: class D
  let cS: class S
  let cF: class F
  let vp: setvar p
  let va: setvar a
  let vb: setvar b

  disjoint S p
  disjoint F p
  disjoint D p
  disjoint S a
  disjoint S b
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint F a
  disjoint F b
  disjoint D a
  disjoint D b
  assert |- ( ( D C_ CC /\ -. D e. Fin ) -> E* p ( p e. ( Poly ` S ) /\ ( p |` D ) = F ) )

  proof
    cD
    cc
    wss
    #
    cD
    cfn
    wcel
    #
    wn
    #
    wa
    #
    vp
    cv
    #
    cc
    cply
    cfv
    #
    wcel
    #
    @4
    cD
    cres
    #
    cF
    wceq
    #
    wa
    #
    vp
    wmo
    #
    @4
    cS
    cply
    cfv
    #
    wcel
    #
    @8
    wa
    #
    vp
    wmo
    @3
    @9
    va
    cv
    #
    @5
    wcel
    #
    @14
    cD
    cres
    #
    cF
    wceq
    #
    wa
    #
    wa
    #
    @4
    @14
    wceq
    #
    wi
    #
    va
    wal
    vp
    wal
    @10
    @3
    @21
    vp
    va
    @3
    @19
    @20
    @3
    @19
    wa
    #
    @4
    @14
    cmin
    cof
    co
    #
    cc
    cc0
    csn
    #
    cxp
    #
    wceq
    #
    @20
    @22
    @23
    c0p
    @25
    @22
    @23
    c0p
    wceq
    #
    @23
    ccnv
    @24
    cima
    #
    cfn
    wcel
    #
    @22
    @29
    @1
    @0
    @2
    @19
    simplr
    @22
    cD
    @28
    wss
    #
    @29
    @1
    wi
    @22
    vb
    cD
    @28
    @22
    vb
    cv
    #
    cD
    wcel
    #
    @31
    cc
    wcel
    #
    @31
    @23
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @31
    @28
    wcel
    #
    @22
    @32
    @33
    @35
    @22
    cD
    cc
    @31
    @0
    @2
    @19
    simpll
    #
    sseld
    @22
    @32
    @35
    @22
    @32
    wa
    #
    @34
    @31
    @4
    cfv
    #
    @31
    @14
    cfv
    #
    cmin
    co
    #
    cc0
    @39
    @4
    cc
    wfn
    #
    @14
    cc
    wfn
    #
    cc
    cvv
    wcel
    #
    @33
    @34
    @42
    wceq
    @22
    @43
    @32
    @22
    cc
    cc
    @4
    wf
    #
    @43
    @22
    @6
    @46
    @3
    @6
    @8
    @18
    simprll
    #
    cc
    @4
    plyf
    syl
    #
    cc
    cc
    @4
    ffn
    syl
    adantr
    @22
    @44
    @32
    @22
    cc
    cc
    @14
    wf
    #
    @44
    @22
    @15
    @49
    @3
    @9
    @15
    @17
    simprrl
    #
    cc
    @14
    plyf
    syl
    #
    cc
    cc
    @14
    ffn
    syl
    adantr
    @45
    @39
    cnex
    a1i
    @22
    cD
    cc
    @31
    @38
    sselda
    #
    cc
    cmin
    @4
    @14
    cvv
    @31
    fnfvof
    syl22anc
    @39
    @40
    @41
    @39
    cc
    cc
    @31
    @4
    @22
    @46
    @32
    @48
    adantr
    @52
    ffvelrnd
    @39
    @31
    @7
    cfv
    #
    @31
    @16
    cfv
    #
    @40
    @41
    @39
    @31
    @7
    @16
    @22
    @7
    @16
    wceq
    @32
    @22
    @7
    cF
    @16
    @3
    @6
    @8
    @18
    simprlr
    @3
    @9
    @15
    @17
    simprrr
    eqtr4d
    adantr
    fveq1d
    @32
    @53
    @40
    wceq
    @22
    @31
    cD
    @4
    fvres
    adantl
    @32
    @54
    @41
    wceq
    @22
    @31
    cD
    @14
    fvres
    adantl
    3eqtr3d
    subeq0bd
    eqtrd
    ex
    jcad
    @22
    @23
    @5
    wcel
    #
    cc
    cc
    @23
    wf
    @23
    cc
    wfn
    @37
    @36
    wb
    @22
    @6
    @15
    @55
    @47
    @50
    cc
    @4
    @14
    plysubcl
    syl2anc
    #
    cc
    @23
    plyf
    cc
    cc
    @23
    ffn
    cc
    cc0
    @31
    @23
    fniniseg
    4syl
    sylibrd
    ssrdv
    @29
    @30
    @1
    @28
    cD
    ssfi
    expcom
    syl
    mtod
    @22
    @27
    wn
    #
    @29
    @22
    @57
    wa
    @29
    @28
    chash
    cfv
    @23
    cdgr
    cfv
    cle
    wbr
    #
    @22
    @55
    @23
    c0p
    wne
    #
    @29
    @58
    wa
    @57
    @56
    @59
    @57
    @23
    c0p
    df-ne
    biimpri
    @28
    cc
    @23
    @28
    eqid
    fta1
    syl2an
    simpld
    ex
    mt3d
    df-0p
    syl6eq
    @22
    @45
    @46
    @49
    @26
    @20
    wb
    @45
    @22
    cnex
    a1i
    @48
    @51
    cc
    @4
    @14
    cvv
    ofsubeq0
    syl3anc
    mpbid
    ex
    alrimivv
    @9
    @18
    vp
    va
    @20
    @6
    @15
    @8
    @17
    @4
    @14
    @5
    eleq1
    @20
    @7
    @16
    cF
    @4
    @14
    cD
    reseq1
    eqeq1d
    anbi12d
    mo4
    sylibr
    @13
    @9
    vp
    @12
    @6
    @8
    @11
    @5
    @4
    cS
    plyssc
    sseli
    anim1i
    moimi
    syl
end
