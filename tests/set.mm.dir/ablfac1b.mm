include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "cvv.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "syl.mm"
include "cprime.mm"
include "wss.mm"
include "cn.mm"
include "nnex.mm"
include "cv.mm"
include "prmnn.mm"
include "ssriv.mm"
include "ssexi.mm"
include "ssex.mm"
include "chash.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "cz.mm"
include "adantr.mm"
include "sselda.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "oddvdssubg.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "w3a.mm"
include "wf.mm"
include "simpr1.mm"
include "ffvelrnd.mm"
include "simpr2.mm"
include "ablcntzd.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "cdiv.mm"
include "wceq.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "eqimss.mm"
include "cmre.mm"
include "cacs.mm"
include "subgacs.mm"
include "acsmre.mm"
include "4syl.mm"
include "cpw.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "cmul.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "pcdvds.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "cgcd.mm"
include "c1.mm"
include "wi.mm"
include "ablfac1lem.mm"
include "simp1d.mm"
include "simpld.mm"
include "eldifsni.mm"
include "necomd.mm"
include "prmrp.mm"
include "cn0.mm"
include "prmz.mm"
include "rpexp12i.mm"
include "syl112anc.mm"
include "mpd.mm"
include "coprmdvds2.mm"
include "syl31anc.mm"
include "mp2and.mm"
include "simp3d.mm"
include "breqtrd.mm"
include "cc0.mm"
include "simprd.mm"
include "nnne0d.mm"
include "dvdscmulr.mm"
include "mpbid.mm"
include "odcl.mm"
include "nn0zd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "ss2rabdv.mm"
include "elpw.mm"
include "sylibr.mm"
include "cmpt.mm"
include "reseq1i.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "frn.mm"
include "syl5eqss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrcsscl.mm"
include "ss2in.mm"
include "clsm.mm"
include "simp2d.mm"
include "ablfacrp.mm"
include "sseqtrd.mm"
include "dmdprdd.mm"

theorem ablfac1b
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cG: class G
  let cO: class O
  let vp: setvar p
  let vq: setvar q
  let vw: setvar w
  let vy: setvar y
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let cP: class P
  let cT: class T
  assume ablfac1.b: |- B = ( Base ` G )
  assume ablfac1.o: |- O = ( od ` G )
  assume ablfac1.s: |- S = ( p e. A |-> { x e. B | ( O ` x ) || ( p ^ ( p pCnt ( # ` B ) ) ) } )
  assume ablfac1.g: |- ( ph -> G e. Abel )
  assume ablfac1.f: |- ( ph -> B e. Fin )
  assume ablfac1.1: |- ( ph -> A C_ Prime )

  disjoint p x
  disjoint B p
  disjoint B x
  disjoint p ph
  disjoint ph x
  disjoint A p
  disjoint A x
  disjoint O p
  disjoint O x
  disjoint G p
  disjoint G x
  disjoint p q
  disjoint p w
  disjoint p y
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint B q
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint x y
  disjoint B y
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p z
  disjoint q z
  disjoint ph q
  disjoint w z
  disjoint ph w
  disjoint x z
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S a
  disjoint S b
  disjoint S q
  disjoint A a
  disjoint A b
  disjoint A q
  disjoint A y
  disjoint A z
  disjoint O q
  disjoint O y
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint T q
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint G a
  disjoint G b
  disjoint G q
  disjoint G y
  disjoint G z
  assert |- ( ph -> G dom DProd S )

  proof
    wph
    va
    vb
    cS
    cG
    cA
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cvv
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    @3
    eqid
    #
    @2
    eqid
    #
    @1
    eqid
    #
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    #
    ablfac1.g
    cG
    ablgrp
    #
    syl
    #
    wph
    cA
    cprime
    wss
    #
    cA
    cvv
    wcel
    ablfac1.1
    cA
    cprime
    cprime
    cn
    nnex
    vp
    cprime
    cn
    vp
    cv
    #
    prmnn
    #
    ssriv
    ssexi
    ssex
    syl
    wph
    vp
    cA
    vx
    cv
    #
    cO
    cfv
    #
    @12
    @12
    cB
    chash
    cfv
    #
    cpc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    @0
    cS
    wph
    @12
    cA
    wcel
    #
    wa
    #
    @7
    @18
    cz
    wcel
    #
    @20
    @0
    wcel
    wph
    @7
    @21
    ablfac1.g
    adantr
    @22
    @18
    @22
    @12
    @17
    @22
    @12
    cprime
    wcel
    #
    @12
    cn
    wcel
    #
    wph
    cA
    cprime
    @12
    ablfac1.1
    sselda
    #
    @13
    syl
    @22
    @12
    @16
    @26
    wph
    @16
    cn
    wcel
    #
    @21
    wph
    @27
    cB
    c0
    wne
    #
    wph
    @8
    @28
    @10
    cB
    cG
    ablfac1.b
    grpbn0
    syl
    wph
    cB
    cfn
    wcel
    @27
    @28
    wb
    ablfac1.f
    cB
    hashnncl
    syl
    mpbird
    #
    adantr
    pccld
    nnexpcld
    nnzd
    vx
    cB
    cG
    @18
    cO
    ablfac1.o
    ablfac1.b
    oddvdssubg
    syl2anc
    ablfac1.s
    fmptd
    #
    wph
    va
    cv
    #
    cA
    wcel
    #
    vb
    cv
    #
    cA
    wcel
    #
    @31
    @33
    wne
    #
    w3a
    #
    wa
    #
    @31
    cS
    cfv
    #
    @33
    cS
    cfv
    cG
    @3
    @4
    wph
    @7
    @36
    ablfac1.g
    adantr
    @37
    cA
    @0
    @31
    cS
    wph
    cA
    @0
    cS
    wf
    @36
    @30
    adantr
    #
    wph
    @32
    @34
    @35
    simpr1
    ffvelrnd
    @37
    cA
    @0
    @33
    cS
    @39
    wph
    @32
    @34
    @35
    simpr2
    ffvelrnd
    ablcntzd
    wph
    @32
    wa
    #
    @38
    cS
    cA
    @31
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    @1
    cfv
    #
    cin
    #
    @15
    @31
    @31
    @16
    cpc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    @15
    @16
    @48
    cdiv
    co
    #
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    cin
    #
    @2
    csn
    #
    @40
    @38
    @50
    wss
    #
    @45
    @53
    wss
    #
    @46
    @54
    wss
    @40
    @38
    @50
    wceq
    #
    @56
    @32
    @58
    wph
    vp
    @31
    @20
    @50
    cA
    cS
    @12
    @31
    wceq
    #
    @19
    @49
    vx
    cB
    @59
    @18
    @48
    @15
    cdvds
    @59
    @12
    @31
    @17
    @47
    cexp
    @59
    id
    @12
    @31
    @16
    cpc
    oveq1
    oveq12d
    breq2d
    rabbidv
    ablfac1.s
    @19
    vx
    cB
    cB
    cG
    cbs
    cfv
    #
    cvv
    ablfac1.b
    cG
    cbs
    fvex
    eqeltri
    rabex
    #
    fvmpt3i
    adantl
    @38
    @50
    eqimss
    syl
    @40
    @0
    @60
    cmre
    cfv
    wcel
    #
    @44
    @53
    wss
    #
    @53
    @0
    wcel
    #
    @57
    @40
    @7
    @8
    @0
    @60
    cacs
    cfv
    wcel
    @62
    wph
    @7
    @32
    ablfac1.g
    adantr
    #
    @9
    @60
    cG
    @60
    eqid
    subgacs
    @0
    @60
    acsmre
    4syl
    @40
    @43
    @53
    cpw
    #
    wss
    @63
    @40
    @43
    cS
    @42
    cres
    #
    crn
    #
    @66
    cS
    @42
    df-ima
    @40
    @42
    @66
    @67
    wf
    @68
    @66
    wss
    @40
    vp
    @42
    @20
    @66
    @67
    @40
    @12
    @42
    wcel
    #
    wa
    #
    @20
    @53
    wss
    @20
    @66
    wcel
    @70
    @19
    @52
    vx
    cB
    @70
    @14
    cB
    wcel
    #
    wa
    #
    @19
    @18
    @51
    cdvds
    wbr
    #
    @52
    @72
    @48
    @18
    cmul
    co
    #
    @48
    @51
    cmul
    co
    #
    cdvds
    wbr
    #
    @73
    @72
    @74
    @16
    @75
    cdvds
    @72
    @48
    @16
    cdvds
    wbr
    #
    @18
    @16
    cdvds
    wbr
    #
    @74
    @16
    cdvds
    wbr
    #
    @72
    @31
    cprime
    wcel
    #
    @27
    @77
    @40
    @80
    @69
    @71
    wph
    cA
    cprime
    @31
    ablfac1.1
    sselda
    ad2antrr
    #
    wph
    @27
    @32
    @69
    @71
    @29
    ad3antrrr
    #
    @31
    @16
    pcdvds
    syl2anc
    @72
    @24
    @27
    @78
    @72
    cA
    cprime
    @12
    wph
    @11
    @32
    @69
    @71
    ablfac1.1
    ad3antrrr
    @69
    @21
    @40
    @71
    @12
    cA
    @41
    eldifi
    ad2antlr
    sseldd
    #
    @82
    @12
    @16
    pcdvds
    syl2anc
    @72
    @48
    cz
    wcel
    #
    @23
    @16
    cz
    wcel
    @48
    @18
    cgcd
    co
    c1
    wceq
    #
    @77
    @78
    wa
    @79
    wi
    @72
    @48
    @40
    @48
    cn
    wcel
    #
    @69
    @71
    @40
    @86
    @51
    cn
    wcel
    #
    @40
    @86
    @87
    wa
    #
    @48
    @51
    cgcd
    co
    c1
    wceq
    #
    @16
    @75
    wceq
    #
    wph
    vx
    cA
    cB
    @31
    cS
    cG
    @48
    @51
    cO
    vp
    ablfac1.b
    ablfac1.o
    ablfac1.s
    ablfac1.g
    ablfac1.f
    ablfac1.1
    @48
    eqid
    @51
    eqid
    ablfac1lem
    #
    simp1d
    #
    simpld
    #
    ad2antrr
    #
    nnzd
    #
    @72
    @18
    @72
    @12
    @17
    @72
    @24
    @25
    @83
    @13
    syl
    @72
    @12
    @16
    @83
    @82
    pccld
    #
    nnexpcld
    nnzd
    #
    @72
    @16
    @82
    nnzd
    @72
    @31
    @12
    cgcd
    co
    c1
    wceq
    #
    @85
    @72
    @98
    @31
    @12
    wne
    #
    @72
    @12
    @31
    @69
    @12
    @31
    wne
    @40
    @71
    @12
    cA
    @31
    eldifsni
    ad2antlr
    necomd
    @72
    @80
    @24
    @98
    @99
    wb
    @81
    @83
    @31
    @12
    prmrp
    syl2anc
    mpbird
    @72
    @31
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @47
    cn0
    wcel
    @17
    cn0
    wcel
    @98
    @85
    wi
    @72
    @80
    @100
    @81
    @31
    prmz
    syl
    @72
    @24
    @101
    @83
    @12
    prmz
    syl
    @72
    @31
    @16
    @81
    @82
    pccld
    @96
    @31
    @12
    @47
    @17
    rpexp12i
    syl112anc
    mpd
    @16
    @48
    @18
    coprmdvds2
    syl31anc
    mp2and
    @40
    @90
    @69
    @71
    @40
    @88
    @89
    @90
    @91
    simp3d
    #
    ad2antrr
    breqtrd
    @72
    @23
    @51
    cz
    wcel
    #
    @84
    @48
    cc0
    wne
    @76
    @73
    wb
    @97
    @72
    @51
    @40
    @87
    @69
    @71
    @40
    @86
    @87
    @92
    simprd
    #
    ad2antrr
    nnzd
    #
    @95
    @72
    @48
    @94
    nnne0d
    @48
    @18
    @51
    dvdscmulr
    syl112anc
    mpbid
    @72
    @15
    cz
    wcel
    @23
    @103
    @19
    @73
    wa
    @52
    wi
    @72
    @15
    @71
    @15
    cn0
    wcel
    @70
    @14
    cG
    cO
    cB
    ablfac1.b
    ablfac1.o
    odcl
    adantl
    nn0zd
    @97
    @105
    @15
    @18
    @51
    dvdstr
    syl3anc
    mpan2d
    ss2rabdv
    @20
    @53
    @61
    elpw
    sylibr
    @67
    vp
    cA
    @20
    cmpt
    #
    @42
    cres
    #
    vp
    @42
    @20
    cmpt
    #
    cS
    @106
    @42
    ablfac1.s
    reseq1i
    @42
    cA
    wss
    @107
    @108
    wceq
    cA
    @41
    difss
    vp
    cA
    @42
    @20
    resmpt
    ax-mp
    eqtri
    fmptd
    @42
    @66
    @67
    frn
    syl
    syl5eqss
    @43
    @53
    sspwuni
    sylib
    @40
    @7
    @103
    @64
    @65
    @40
    @51
    @104
    nnzd
    vx
    cB
    cG
    @51
    cO
    ablfac1.o
    ablfac1.b
    oddvdssubg
    syl2anc
    @0
    @44
    @1
    @53
    @60
    @6
    mrcsscl
    syl3anc
    @38
    @50
    @45
    @53
    ss2in
    syl2anc
    @40
    @54
    @55
    wceq
    @50
    @53
    cG
    clsm
    cfv
    #
    co
    cB
    wceq
    @40
    vx
    cB
    @109
    cG
    @50
    @53
    @48
    @51
    cO
    @2
    ablfac1.b
    ablfac1.o
    @50
    eqid
    @53
    eqid
    @65
    @93
    @104
    @40
    @88
    @89
    @90
    @91
    simp2d
    @102
    @5
    @109
    eqid
    ablfacrp
    simpld
    sseqtrd
    dmdprdd
end
