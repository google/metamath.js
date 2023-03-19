include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "cn0.mm"
include "csu.mm"
include "cvv.mm"
include "sumex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "wa.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cres.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wss.mm"
include "ccnv.mm"
include "cico.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "0cn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "sylancr.mm"
include "abssub.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "c1.mm"
include "cif.mm"
include "breq2.mm"
include "cle.mm"
include "w3a.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylib.mm"
include "simprd.mm"
include "cxr.mm"
include "0re.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "radcnvcl.mm"
include "adantr.mm"
include "sseldi.mm"
include "elico2.mm"
include "mpbid.mm"
include "simp3d.mm"
include "abscld.mm"
include "avglt1.mm"
include "sylan.mm"
include "wn.mm"
include "ltp1d.mm"
include "ifbothda.mm"
include "syl6breqr.mm"
include "eqbrtrd.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "crp.mm"
include "psercnlem1.mm"
include "simp1d.mm"
include "rpxrd.mm"
include "elbl.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "fvres.mm"
include "syl.mm"
include "cmpt.mm"
include "reseq1i.mm"
include "psercnlem2.mm"
include "simp2d.mm"
include "sstrd.mm"
include "resmptd.mm"
include "syl5eq.mm"
include "cseq.mm"
include "weq.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "mpteq2dv.mm"
include "rpred.mm"
include "psercn2.mm"
include "eqeltrd.mm"
include "cncff.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "cuni.mm"
include "syl6ss.mm"
include "ssid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "restuni.mm"
include "cncnpi.mm"
include "syl2anc.mm"
include "cnex.mm"
include "ssexi.mm"
include "restabs.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "cnt.mm"
include "resttop.mm"
include "mp2an.mm"
include "cin.mm"
include "df-ss.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "elrestr.mm"
include "isopn3i.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "ctopon.mm"
include "resttopon.mm"
include "cncnp.mm"
include "syl6eleqr.mm"

theorem psercn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  let cB: class B
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume psercn.s: |- S = ( `' abs " ( 0 [,) R ) )
  assume psercn.m: |- M = if ( R e. RR , ( ( ( abs ` a ) + R ) / 2 ) , ( ( abs ` a ) + 1 ) )

  disjoint a j
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M j
  disjoint M y
  disjoint G j
  disjoint G r
  disjoint G y
  disjoint S a
  disjoint S j
  disjoint S y
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint ph y
  disjoint a k
  disjoint a m
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint M i
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint M k
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint i x
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint i r
  disjoint G i
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S i
  disjoint S k
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint i ph
  disjoint k ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ph -> F e. ( S -cn-> CC ) )

  proof
    wph
    cF
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @0
    ccn
    co
    #
    cS
    cc
    ccncf
    co
    #
    wph
    cS
    cc
    cF
    wf
    #
    cF
    va
    cv
    #
    @1
    @0
    ccnp
    co
    cfv
    wcel
    #
    va
    cS
    wral
    #
    cF
    @2
    wcel
    #
    wph
    cF
    cS
    wfn
    #
    @5
    cF
    cfv
    #
    cc
    wcel
    #
    va
    cS
    wral
    @4
    cn0
    vj
    cv
    vy
    cv
    #
    cG
    cfv
    #
    cfv
    #
    vj
    csu
    #
    cvv
    wcel
    #
    vy
    cS
    wral
    @9
    wph
    @16
    vy
    cS
    cn0
    @14
    vj
    sumex
    rgenw
    vy
    cS
    @15
    cF
    cvv
    pserf.f
    fnmpt
    mp1i
    wph
    @11
    va
    cS
    wph
    @5
    cS
    wcel
    #
    wa
    #
    @5
    cF
    cc0
    cM
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cres
    #
    cfv
    #
    @10
    cc
    @18
    @5
    @20
    wcel
    #
    @22
    @10
    wceq
    @18
    @23
    @5
    cc
    wcel
    #
    cc0
    @5
    @19
    co
    #
    cM
    clt
    wbr
    #
    wph
    cS
    cc
    @5
    cS
    cc
    wss
    #
    wph
    cS
    cabs
    ccnv
    #
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @30
    cabs
    cdm
    cc
    cabs
    @29
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    eqsstri
    #
    a1i
    sselda
    #
    @18
    @25
    @5
    cabs
    cfv
    #
    cM
    clt
    @18
    @25
    cc0
    @5
    cmin
    co
    cabs
    cfv
    #
    @5
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @33
    @18
    cc0
    cc
    wcel
    #
    @24
    @25
    @34
    wceq
    0cn
    @32
    cc0
    @5
    @19
    @19
    eqid
    cnmetdval
    sylancr
    @18
    @37
    @24
    @34
    @36
    wceq
    0cn
    @32
    cc0
    @5
    abssub
    sylancr
    @18
    @35
    @5
    cabs
    @18
    @5
    @32
    subid1d
    fveq2d
    3eqtrd
    @18
    @33
    cR
    cr
    wcel
    #
    @33
    cR
    caddc
    co
    c2
    cdiv
    co
    #
    @33
    c1
    caddc
    co
    #
    cif
    #
    cM
    clt
    @38
    @33
    @39
    clt
    wbr
    #
    @33
    @40
    clt
    wbr
    #
    @33
    @41
    clt
    wbr
    @18
    @39
    @40
    @39
    @41
    @33
    clt
    breq2
    @40
    @41
    @33
    clt
    breq2
    @18
    @38
    wa
    @33
    cR
    clt
    wbr
    #
    @42
    @18
    @44
    @38
    @18
    @33
    cr
    wcel
    #
    cc0
    @33
    cle
    wbr
    #
    @44
    @18
    @33
    @29
    wcel
    #
    @45
    @46
    @44
    w3a
    #
    @18
    @24
    @47
    @18
    @5
    @30
    wcel
    #
    @24
    @47
    wa
    #
    @18
    @5
    cS
    @30
    wph
    @17
    simpr
    psercn.s
    syl6eleq
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @49
    @50
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @5
    @29
    cabs
    elpreima
    mp2b
    sylib
    simprd
    @18
    cc0
    cr
    wcel
    cR
    cxr
    wcel
    @47
    @48
    wb
    0re
    @18
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cR
    cc0
    cpnf
    iccssxr
    wph
    cR
    @51
    wcel
    @17
    wph
    vx
    cA
    cR
    vn
    cG
    vr
    pserf.g
    pserf.a
    pserf.r
    radcnvcl
    adantr
    sseldi
    cc0
    cR
    @33
    elico2
    sylancr
    mpbid
    simp3d
    adantr
    @18
    @45
    @38
    @44
    @42
    wb
    @18
    @5
    @32
    abscld
    #
    @33
    cR
    avglt1
    sylan
    mpbid
    @18
    @43
    @38
    wn
    @18
    @33
    @52
    ltp1d
    adantr
    ifbothda
    psercn.m
    syl6breqr
    eqbrtrd
    @18
    @19
    cc
    cxmt
    cfv
    wcel
    #
    @37
    cM
    cxr
    wcel
    #
    @23
    @24
    @26
    wa
    wb
    @53
    @18
    cnxmet
    a1i
    #
    @37
    @18
    0cn
    a1i
    #
    @18
    cM
    @18
    cM
    crp
    wcel
    #
    @33
    cM
    clt
    wbr
    #
    cM
    cR
    clt
    wbr
    #
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    psercnlem1
    #
    simp1d
    #
    rpxrd
    #
    @5
    @19
    cc0
    cM
    cc
    elbl
    syl3anc
    mpbir2and
    #
    @5
    @20
    cF
    fvres
    syl
    @18
    @20
    cc
    @5
    @21
    @18
    @21
    @20
    cc
    ccncf
    co
    #
    wcel
    @20
    cc
    @21
    wf
    @18
    @21
    vy
    @20
    @15
    cmpt
    #
    @64
    @18
    @21
    vy
    cS
    @15
    cmpt
    #
    @20
    cres
    @65
    cF
    @66
    @20
    pserf.f
    reseq1i
    @18
    vy
    cS
    @20
    @15
    @18
    @20
    @28
    cc0
    cM
    cicc
    co
    cima
    #
    cS
    @18
    @23
    @20
    @67
    wss
    #
    @67
    cS
    wss
    #
    wph
    vx
    vy
    cA
    cR
    cS
    vj
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    @60
    psercnlem2
    #
    simp2d
    #
    @18
    @23
    @68
    @69
    @70
    simp3d
    sstrd
    #
    resmptd
    syl5eq
    @18
    vx
    vy
    cA
    cR
    @20
    vi
    vj
    vn
    @65
    cG
    vs
    cn0
    vk
    @20
    vs
    cv
    #
    caddc
    vk
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    cmpt
    cM
    vr
    pserf.g
    @65
    eqid
    wph
    cn0
    cc
    cA
    wf
    @17
    pserf.a
    adantr
    pserf.r
    vs
    vi
    cn0
    @78
    vy
    @20
    vi
    cv
    #
    caddc
    @13
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    vs
    vi
    weq
    #
    @78
    vy
    @20
    @73
    @80
    cfv
    #
    cmpt
    @82
    vk
    vy
    @20
    @77
    @84
    vk
    vy
    weq
    #
    @73
    @76
    @80
    @85
    @75
    @13
    caddc
    cc0
    @74
    @12
    cG
    fveq2
    seqeq3d
    fveq1d
    cbvmptv
    @83
    vy
    @20
    @84
    @81
    @73
    @79
    @80
    fveq2
    mpteq2dv
    syl5eq
    cbvmptv
    @18
    cM
    @61
    rpred
    @18
    @57
    @58
    @59
    @60
    simp3d
    @71
    psercn2
    eqeltrd
    #
    @20
    cc
    @21
    cncff
    syl
    @63
    ffvelrnd
    eqeltrrd
    ralrimiva
    va
    cS
    cc
    cF
    ffnfv
    sylanbrc
    #
    wph
    @6
    va
    cS
    @18
    @6
    @21
    @5
    @1
    @20
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @18
    @21
    @5
    @0
    @20
    crest
    co
    #
    @0
    ccnp
    co
    #
    cfv
    #
    @90
    @18
    @21
    @92
    @0
    ccn
    co
    #
    wcel
    @5
    @92
    cuni
    #
    wcel
    @21
    @94
    wcel
    @18
    @21
    @64
    @95
    @86
    @18
    @20
    cc
    wss
    #
    cc
    cc
    wss
    #
    @64
    @95
    wceq
    @18
    @20
    cS
    cc
    @72
    @31
    syl6ss
    #
    cc
    ssid
    #
    @20
    cc
    @0
    @92
    @0
    @0
    eqid
    #
    @92
    eqid
    @0
    cc
    crest
    co
    #
    @0
    @0
    ctop
    wcel
    #
    @102
    @0
    wceq
    @0
    @101
    cnfldtop
    #
    @0
    ctop
    cc
    cc
    @0
    @0
    @101
    cnfldtopon
    #
    toponunii
    #
    restid
    ax-mp
    eqcomi
    #
    cncfcn
    sylancl
    eleqtrd
    @18
    @5
    @20
    @96
    @63
    @18
    @103
    @97
    @20
    @96
    wceq
    @104
    @99
    @20
    @0
    cc
    @106
    restuni
    sylancr
    eleqtrd
    @5
    @21
    @92
    @0
    @96
    @96
    eqid
    cncnpi
    syl2anc
    @18
    @5
    @89
    @93
    @18
    @88
    @92
    @0
    ccnp
    @18
    @103
    @20
    cS
    wss
    #
    cS
    cvv
    wcel
    #
    @88
    @92
    wceq
    @103
    @18
    @104
    a1i
    #
    @72
    @109
    @18
    cS
    cc
    cnex
    @31
    ssexi
    #
    a1i
    #
    @20
    cS
    @0
    ctop
    cvv
    restabs
    syl3anc
    oveq1d
    fveq1d
    eleqtrrd
    @18
    @1
    ctop
    wcel
    #
    @108
    @5
    @20
    @1
    cnt
    cfv
    cfv
    #
    wcel
    @4
    @6
    @91
    wb
    @113
    @18
    @103
    @109
    @113
    @104
    @111
    cS
    @0
    cvv
    resttop
    mp2an
    #
    a1i
    @72
    @18
    @5
    @20
    @114
    @63
    @18
    @113
    @20
    @1
    wcel
    @114
    @20
    wceq
    @115
    @18
    @20
    cS
    cin
    #
    @20
    @1
    @18
    @108
    @116
    @20
    wceq
    @72
    @20
    cS
    df-ss
    sylib
    @18
    @103
    @109
    @20
    @0
    wcel
    #
    @116
    @1
    wcel
    @110
    @112
    @18
    @53
    @37
    @54
    @117
    @55
    @56
    @62
    @19
    cc0
    cM
    @0
    cc
    @0
    @101
    cnfldtopn
    blopn
    syl3anc
    @20
    cS
    @0
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    @20
    @1
    isopn3i
    sylancr
    eleqtrrd
    wph
    @4
    @17
    @87
    adantr
    @20
    @5
    cF
    @1
    @0
    cS
    cc
    @103
    @27
    cS
    @1
    cuni
    wceq
    @104
    @31
    cS
    @0
    cc
    @106
    restuni
    mp2an
    @106
    cnprest
    syl22anc
    mpbird
    ralrimiva
    @1
    cS
    ctopon
    cfv
    wcel
    #
    @0
    cc
    ctopon
    cfv
    wcel
    #
    @8
    @4
    @7
    wa
    wb
    @119
    @27
    @118
    @105
    @31
    cS
    @0
    cc
    resttopon
    mp2an
    @105
    va
    cF
    @1
    @0
    cS
    cc
    cncnp
    mp2an
    sylanbrc
    @27
    @98
    @3
    @2
    wceq
    @31
    @100
    cS
    cc
    @0
    @1
    @0
    @101
    @1
    eqid
    @107
    cncfcn
    mp2an
    syl6eleqr
end
