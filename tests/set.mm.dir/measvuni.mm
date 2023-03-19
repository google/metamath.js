include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "crab.mm"
include "ciun.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cesum.mm"
include "wceq.mm"
include "simp1.mm"
include "cv.mm"
include "rabid.mm"
include "simprbi.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "ssrab2.mm"
include "ssct.mm"
include "mpan.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "simp3r.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "disjss1f.mm"
include "mpsyl.mm"
include "measvunilem0.mm"
include "syl112anc.mm"
include "measvunilem.mm"
include "oveq12d.mm"
include "cun.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "nf3an.mm"
include "nfun.mm"
include "wo.mm"
include "simp2.mm"
include "rabid2.mm"
include "sylibr.mm"
include "elun.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "measbase.mm"
include "0elsiga.mm"
include "snssi.mm"
include "3syl.mm"
include "undif.mm"
include "sylib.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "rabbidv.mm"
include "eqtr4d.mm"
include "unrab.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "iuneq12df.mm"
include "fveq2d.mm"
include "iunxun.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "cin.mm"
include "wb.mm"
include "elsni.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "syl2an.mm"
include "sigaclcuni.mm"
include "syl3anc.mm"
include "eldifad.mm"
include "syl.mm"
include "iuneq2i.mm"
include "iun0.mm"
include "eqtri.mm"
include "ineq1.mm"
include "0in.mm"
include "mp1i.mm"
include "measun.mm"
include "syl121anc.mm"
include "eqtrd.mm"
include "esumeq1d.mm"
include "cvv.mm"
include "ctex.mm"
include "inrab.mm"
include "wn.mm"
include "noel.mm"
include "disjdif.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "elin.mm"
include "mtbi.mm"
include "rgenw.mm"
include "rabeq0.mm"
include "mpbir.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "sylan.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "esumsplit.mm"
include "3eqtr4d.mm"

theorem measvuni
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M

  disjoint A x
  disjoint M x
  disjoint S x
  assert |- ( ( M e. ( measures ` S ) /\ A. x e. A B e. S /\ ( A ~<_ _om /\ Disj_ x e. A B ) ) -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cB
    cS
    wcel
    #
    vx
    cA
    wral
    #
    cA
    com
    cdom
    wbr
    #
    vx
    cA
    cB
    wdisj
    #
    wa
    #
    w3a
    #
    vx
    cB
    c0
    csn
    #
    wcel
    #
    vx
    cA
    crab
    #
    cB
    ciun
    #
    cM
    cfv
    #
    vx
    cB
    cS
    @7
    cdif
    #
    wcel
    #
    vx
    cA
    crab
    #
    cB
    ciun
    #
    cM
    cfv
    #
    cxad
    co
    #
    @9
    cB
    cM
    cfv
    #
    vx
    cesum
    #
    @14
    @18
    vx
    cesum
    #
    cxad
    co
    #
    vx
    cA
    cB
    ciun
    #
    cM
    cfv
    #
    cA
    @18
    vx
    cesum
    #
    @6
    @11
    @19
    @16
    @20
    cxad
    @6
    @0
    @8
    vx
    @9
    wral
    #
    @9
    com
    cdom
    wbr
    #
    vx
    @9
    cB
    wdisj
    #
    @11
    @19
    wceq
    @0
    @2
    @5
    simp1
    #
    @0
    @2
    @25
    @5
    @0
    @8
    vx
    @9
    vx
    cv
    #
    @9
    wcel
    #
    @8
    @0
    @30
    @29
    cA
    wcel
    #
    @8
    @8
    vx
    cA
    rabid
    simprbi
    #
    adantl
    ralrimiva
    3ad2ant1
    @5
    @0
    @26
    @2
    @3
    @26
    @4
    @9
    cA
    wss
    #
    @3
    @26
    @8
    vx
    cA
    ssrab2
    #
    @9
    cA
    ssct
    mpan
    adantr
    3ad2ant3
    #
    @33
    @6
    @4
    @27
    @34
    @0
    @2
    @3
    @4
    simp3r
    #
    vx
    @9
    cA
    cB
    @8
    vx
    cA
    nfrab1
    #
    vx
    cA
    nfcv
    #
    disjss1f
    mpsyl
    vx
    @9
    cB
    cS
    cM
    @37
    measvunilem0
    syl112anc
    @6
    @0
    @13
    vx
    @14
    wral
    #
    @14
    com
    cdom
    wbr
    #
    vx
    @14
    cB
    wdisj
    #
    @16
    @20
    wceq
    @28
    @0
    @2
    @39
    @5
    @0
    @13
    vx
    @14
    @29
    @14
    wcel
    #
    @13
    @0
    @42
    @31
    @13
    @13
    vx
    cA
    rabid
    simprbi
    #
    adantl
    #
    ralrimiva
    3ad2ant1
    @5
    @0
    @40
    @2
    @3
    @40
    @4
    @14
    cA
    wss
    #
    @3
    @40
    @13
    vx
    cA
    ssrab2
    #
    @14
    cA
    ssct
    mpan
    adantr
    3ad2ant3
    #
    @45
    @6
    @4
    @41
    @46
    @36
    vx
    @14
    cA
    cB
    @13
    vx
    cA
    nfrab1
    #
    @38
    disjss1f
    mpsyl
    vx
    @14
    cB
    cS
    cM
    @48
    measvunilem
    syl112anc
    oveq12d
    @6
    @23
    @10
    @15
    cun
    #
    cM
    cfv
    #
    @17
    @6
    @23
    vx
    @9
    @14
    cun
    #
    cB
    ciun
    #
    cM
    cfv
    @50
    @6
    @22
    @52
    cM
    @6
    vx
    cA
    @51
    cB
    cB
    @0
    @2
    @5
    vx
    @0
    vx
    nfv
    @1
    vx
    cA
    nfra1
    @3
    @4
    vx
    @3
    vx
    nfv
    vx
    cA
    cB
    nfdisj1
    nfan
    nf3an
    #
    @38
    vx
    @9
    @14
    @37
    @48
    nfun
    @6
    cA
    @8
    @13
    wo
    #
    vx
    cA
    crab
    #
    @51
    @6
    cA
    @1
    vx
    cA
    crab
    #
    @55
    @6
    @2
    cA
    @56
    wceq
    @0
    @2
    @5
    simp2
    @1
    vx
    cA
    rabid2
    sylibr
    @0
    @2
    @55
    @56
    wceq
    @5
    @0
    @54
    @1
    vx
    cA
    @54
    cB
    @7
    @12
    cun
    #
    wcel
    @0
    @1
    cB
    @7
    @12
    elun
    @0
    @57
    cS
    cB
    @0
    @7
    cS
    wss
    #
    @57
    cS
    wceq
    @0
    cS
    csiga
    crn
    cuni
    wcel
    #
    c0
    cS
    wcel
    #
    @58
    cS
    cM
    measbase
    #
    cS
    0elsiga
    #
    c0
    cS
    snssi
    3syl
    @7
    cS
    undif
    sylib
    eleq2d
    syl5bbr
    rabbidv
    3ad2ant1
    eqtr4d
    @8
    @13
    vx
    cA
    unrab
    syl6eqr
    #
    @6
    cB
    eqidd
    iuneq12df
    fveq2d
    @52
    @49
    cM
    vx
    @9
    @14
    cB
    iunxun
    fveq2i
    syl6eq
    @6
    @0
    @10
    cS
    wcel
    #
    @15
    cS
    wcel
    #
    @10
    @15
    cin
    #
    c0
    wceq
    #
    @50
    @17
    wceq
    @28
    @6
    @59
    @1
    vx
    @9
    wral
    #
    @26
    @64
    @0
    @2
    @59
    @5
    @61
    3ad2ant1
    #
    @0
    @2
    @68
    @5
    @0
    @1
    vx
    @9
    @0
    @59
    @8
    @1
    @30
    @61
    @32
    @59
    @8
    wa
    @1
    @60
    @59
    @60
    @8
    @62
    adantr
    @8
    @1
    @60
    wb
    @59
    @8
    cB
    c0
    cS
    cB
    c0
    elsni
    #
    eleq1d
    adantl
    mpbird
    syl2an
    #
    ralrimiva
    3ad2ant1
    @35
    @9
    cB
    cS
    vx
    @37
    sigaclcuni
    syl3anc
    @6
    @59
    @1
    vx
    @14
    wral
    #
    @40
    @65
    @69
    @0
    @2
    @72
    @5
    @0
    @1
    vx
    @14
    @0
    @42
    wa
    cB
    cS
    @7
    @44
    eldifad
    ralrimiva
    3ad2ant1
    @47
    @14
    cB
    cS
    vx
    @48
    sigaclcuni
    syl3anc
    @10
    c0
    wceq
    #
    @67
    @6
    @10
    vx
    @9
    c0
    ciun
    c0
    vx
    @9
    cB
    c0
    @30
    @8
    cB
    c0
    wceq
    @32
    @70
    syl
    iuneq2i
    vx
    @9
    iun0
    eqtri
    @73
    @66
    c0
    @15
    cin
    c0
    @10
    c0
    @15
    ineq1
    @15
    0in
    syl6eq
    mp1i
    @10
    @15
    cS
    cM
    measun
    syl121anc
    eqtrd
    @6
    @24
    @51
    @18
    vx
    cesum
    @21
    @6
    cA
    @51
    @18
    vx
    @53
    @63
    esumeq1d
    @6
    @9
    @14
    @18
    vx
    @53
    @37
    @48
    @6
    @26
    @9
    cvv
    wcel
    @35
    @9
    ctex
    syl
    @6
    @40
    @14
    cvv
    wcel
    @47
    @14
    ctex
    syl
    @9
    @14
    cin
    #
    c0
    wceq
    @6
    @74
    @8
    @13
    wa
    #
    vx
    cA
    crab
    #
    c0
    @8
    @13
    vx
    cA
    inrab
    @76
    c0
    wceq
    @75
    wn
    #
    vx
    cA
    wral
    @77
    vx
    cA
    cB
    @7
    @12
    cin
    #
    wcel
    #
    @75
    @79
    cB
    c0
    wcel
    cB
    noel
    @78
    c0
    cB
    @7
    cS
    disjdif
    eleq2i
    mtbir
    cB
    @7
    @12
    elin
    mtbi
    rgenw
    @75
    vx
    cA
    rabeq0
    mpbir
    eqtri
    a1i
    @6
    @30
    wa
    @0
    @1
    @18
    cc0
    cpnf
    cicc
    co
    wcel
    #
    @6
    @0
    @30
    @28
    adantr
    @6
    @0
    @30
    @1
    @28
    @71
    sylan
    cB
    cS
    cM
    measvxrge0
    #
    syl2anc
    @6
    @42
    wa
    #
    @0
    @1
    @80
    @6
    @0
    @42
    @28
    adantr
    @82
    cB
    cS
    @7
    @42
    @13
    @6
    @43
    adantl
    eldifad
    @81
    syl2anc
    esumsplit
    eqtrd
    3eqtr4d
end
