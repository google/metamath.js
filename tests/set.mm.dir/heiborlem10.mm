include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wcel.mm"
include "wn.mm"
include "cc0.mm"
include "co.mm"
include "cfv.mm"
include "wi.mm"
include "ciun.mm"
include "cn0.mm"
include "wf.mm"
include "0nn0.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "sylancl.mm"
include "wral.mm"
include "fveq2.mm"
include "oveq2.mm"
include "iuneq12d.mm"
include "eqeq2d.mm"
include "rspccva.mm"
include "eqimss.mm"
include "syl.mm"
include "w3a.mm"
include "ovex.mm"
include "heiborlem1.mm"
include "weq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "3expia.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wbr.mm"
include "vex.mm"
include "c0ex.mm"
include "heiborlem2.mm"
include "c2nd.mm"
include "c1.mm"
include "caddc.mm"
include "wex.mm"
include "heiborlem3.mm"
include "ad2antrr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cn.mm"
include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cop.mm"
include "cms.mm"
include "simprr.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq12d.mm"
include "ineq12d.mm"
include "anbi12d.mm"
include "cbvralv.mm"
include "simprl.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "eqid.mm"
include "simplrl.mm"
include "cme.mm"
include "cxmt.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "mopnuni.mm"
include "4syl.mm"
include "eqtr2d.mm"
include "heiborlem9.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "sylan2br.mm"
include "3exp2.mm"
include "mpi.mm"
include "rexlimdv.mm"
include "syld.mm"
include "pm2.01d.mm"
include "wb.mm"
include "cdm.mm"
include "elfvdm.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "elab2g.mm"
include "3syl.mm"
include "con2bid.mm"
include "mpbird.mm"
include "sseq1d.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "sstr.mm"
include "unissd.mm"
include "syl2anr.mm"
include "biantrud.mm"
include "eqss.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem heiborlem10
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cD: class D
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let vg: setvar g
  let cM: class M
  let cT: class T
  let wps: wff ps
  let cS: class S
  let cC: class C
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heibor.4: |- G = { <. y , n >. | ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) }
  assume heibor.5: |- B = ( z e. X , m e. NN0 |-> ( z ( ball ` D ) ( 1 / ( 2 ^ m ) ) ) )
  assume heibor.6: |- ( ph -> D e. ( CMet ` X ) )
  assume heibor.7: |- ( ph -> F : NN0 --> ( ~P X i^i Fin ) )
  assume heibor.8: |- ( ph -> A. n e. NN0 X = U_ y e. ( F ` n ) ( y B n ) )

  disjoint ph v
  disjoint n y
  disjoint n u
  disjoint F n
  disjoint u y
  disjoint F u
  disjoint F y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint u v
  disjoint u z
  disjoint D u
  disjoint v y
  disjoint v z
  disjoint D v
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint J m
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J y
  disjoint J z
  disjoint U n
  disjoint U u
  disjoint U v
  disjoint U y
  disjoint U z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  disjoint K n
  disjoint K y
  disjoint K z
  disjoint B x
  disjoint n t
  disjoint n x
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint u x
  disjoint F x
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint G x
  disjoint g r
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint v x
  disjoint x z
  disjoint D x
  disjoint M g
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M t
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J k
  disjoint J r
  disjoint J t
  disjoint J x
  disjoint U g
  disjoint U t
  disjoint U x
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X g
  disjoint X k
  disjoint X r
  disjoint X t
  disjoint X x
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint K g
  disjoint K t
  disjoint K x
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( ( ph /\ ( U C_ J /\ U. J = U. U ) ) -> E. v e. ( ~P U i^i Fin ) U. J = U. v )

  proof
    wph
    cU
    cJ
    wss
    #
    cJ
    cuni
    #
    cU
    cuni
    #
    wceq
    #
    wa
    #
    wa
    #
    cX
    vv
    cv
    #
    cuni
    #
    wss
    #
    vv
    cU
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @1
    @7
    wceq
    #
    vv
    @10
    wrex
    @5
    @11
    cX
    cK
    wcel
    #
    wn
    #
    @5
    @13
    @5
    @13
    vx
    cv
    #
    cc0
    cB
    co
    #
    cK
    wcel
    #
    vx
    cc0
    cF
    cfv
    #
    wrex
    #
    @14
    wph
    @13
    @19
    wi
    #
    @4
    wph
    @18
    cfn
    wcel
    #
    cX
    vy
    @18
    vy
    cv
    #
    cc0
    cB
    co
    #
    ciun
    #
    wss
    #
    @20
    wph
    cn0
    cX
    cpw
    #
    cfn
    cin
    #
    cF
    wf
    #
    cc0
    cn0
    wcel
    #
    @21
    heibor.7
    0nn0
    @28
    @29
    wa
    @27
    cfn
    @18
    @26
    cfn
    inss2
    cn0
    @27
    cc0
    cF
    ffvelrn
    sseldi
    sylancl
    wph
    cX
    @24
    wceq
    #
    @25
    wph
    cX
    vy
    vn
    cv
    #
    cF
    cfv
    #
    @22
    @31
    cB
    co
    #
    ciun
    #
    wceq
    #
    vn
    cn0
    wral
    #
    @29
    @30
    heibor.8
    0nn0
    @35
    @30
    vn
    cc0
    cn0
    @31
    cc0
    wceq
    #
    @34
    @24
    cX
    @37
    vy
    @32
    @18
    @33
    @23
    @31
    cc0
    cF
    fveq2
    @31
    cc0
    @22
    cB
    oveq2
    iuneq12d
    eqeq2d
    rspccva
    sylancl
    cX
    @24
    eqimss
    syl
    @21
    @25
    @13
    @19
    @21
    @25
    @13
    w3a
    @23
    cK
    wcel
    #
    vy
    @18
    wrex
    @19
    vy
    vv
    vu
    @18
    @23
    cX
    cD
    cU
    cJ
    cK
    heibor.1
    heibor.3
    @22
    cc0
    cB
    ovex
    heiborlem1
    @38
    @17
    vy
    vx
    @18
    vy
    vx
    weq
    @23
    @16
    cK
    @22
    @15
    cc0
    cB
    oveq1
    eleq1d
    cbvrexv
    sylib
    3expia
    syl2anc
    adantr
    @5
    @17
    @14
    vx
    @18
    @5
    @29
    @15
    @18
    wcel
    #
    @17
    @14
    wi
    wi
    0nn0
    @5
    @29
    @39
    @17
    @14
    @29
    @39
    @17
    w3a
    @5
    @15
    cc0
    cG
    wbr
    #
    @14
    vy
    vv
    vu
    @15
    cB
    cc0
    cD
    cU
    vn
    cF
    cG
    cJ
    cK
    heibor.1
    heibor.3
    heibor.4
    vx
    vex
    c0ex
    heiborlem2
    @5
    @40
    wa
    #
    @15
    vg
    cv
    #
    cfv
    #
    @15
    c2nd
    cfv
    #
    c1
    caddc
    co
    #
    cG
    wbr
    #
    @15
    cB
    cfv
    #
    @43
    @45
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    vx
    cG
    wral
    #
    vg
    wex
    #
    @14
    wph
    @53
    @4
    @40
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cD
    cU
    vg
    vm
    vn
    cF
    cG
    cJ
    cK
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heiborlem3
    ad2antrr
    @41
    @52
    @14
    vg
    @5
    @40
    @52
    @14
    @5
    @40
    @52
    wa
    #
    wa
    #
    @14
    vt
    vy
    vz
    vv
    vu
    cB
    @15
    cD
    @42
    vg
    cn0
    @42
    cc0
    wceq
    #
    @15
    @42
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cc0
    cseq
    #
    @42
    cU
    vm
    vn
    cF
    cG
    cJ
    cK
    vn
    cn
    @31
    @60
    cfv
    c3
    c2
    @31
    cexp
    co
    cdiv
    co
    cop
    cmpt
    #
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    @4
    @54
    heibor.6
    ad2antrr
    wph
    @28
    @4
    @54
    heibor.7
    ad2antrr
    wph
    @36
    @4
    @54
    heibor.8
    ad2antrr
    @55
    @52
    vt
    cv
    #
    @42
    cfv
    #
    @63
    c2nd
    cfv
    #
    c1
    caddc
    co
    #
    cG
    wbr
    #
    @63
    cB
    cfv
    #
    @64
    @66
    cB
    co
    #
    cin
    #
    cK
    wcel
    #
    wa
    #
    vt
    cG
    wral
    @5
    @40
    @52
    simprr
    @51
    @72
    vx
    vt
    cG
    vx
    vt
    weq
    #
    @46
    @67
    @50
    @71
    @73
    @43
    @64
    @45
    @66
    cG
    @15
    @63
    @42
    fveq2
    #
    @73
    @44
    @65
    c1
    caddc
    @15
    @63
    c2nd
    fveq2
    oveq1d
    #
    breq12d
    @73
    @49
    @70
    cK
    @73
    @47
    @68
    @48
    @69
    @15
    @63
    cB
    fveq2
    @73
    @43
    @64
    @45
    @66
    cB
    @74
    @75
    oveq12d
    ineq12d
    eleq1d
    anbi12d
    cbvralv
    sylib
    @5
    @40
    @52
    simprl
    @59
    vm
    cn0
    vm
    cv
    #
    cc0
    wceq
    #
    @15
    @76
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    wceq
    @60
    @42
    @80
    cc0
    cseq
    wceq
    vg
    vm
    cn0
    @58
    @79
    vg
    vm
    weq
    @56
    @77
    @57
    @78
    @15
    @42
    @76
    cc0
    eqeq1
    @42
    @76
    c1
    cmin
    oveq1
    ifbieq2d
    cbvmptv
    @42
    @59
    @80
    cc0
    seqeq3
    ax-mp
    @61
    eqid
    wph
    @0
    @3
    @54
    simplrl
    @5
    @2
    cX
    wceq
    @54
    @5
    cX
    @1
    @2
    wph
    cX
    @1
    wceq
    #
    @4
    wph
    @62
    cD
    cX
    cme
    cfv
    wcel
    cD
    cX
    cxmt
    cfv
    wcel
    @81
    heibor.6
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    cD
    cJ
    cX
    heibor.1
    mopnuni
    4syl
    #
    adantr
    wph
    @0
    @3
    simprr
    eqtr2d
    adantr
    heiborlem9
    expr
    exlimdv
    mpd
    sylan2br
    3exp2
    mpi
    rexlimdv
    syld
    pm2.01d
    @5
    @13
    @11
    wph
    @13
    @11
    wn
    #
    wb
    #
    @4
    wph
    @62
    cX
    cms
    cdm
    #
    wcel
    @84
    heibor.6
    cD
    cX
    cms
    elfvdm
    vu
    cv
    #
    @7
    wss
    #
    vv
    @10
    wrex
    #
    wn
    @83
    vu
    cX
    cK
    @85
    @86
    cX
    wceq
    #
    @88
    @11
    @89
    @87
    @8
    vv
    @10
    @86
    cX
    @7
    sseq1
    rexbidv
    notbid
    heibor.3
    elab2g
    3syl
    adantr
    con2bid
    mpbird
    @5
    @8
    @12
    vv
    @10
    @5
    @6
    @10
    wcel
    #
    wa
    #
    @8
    @1
    @7
    wss
    #
    @12
    @91
    cX
    @1
    @7
    wph
    @81
    @4
    @90
    @82
    ad2antrr
    sseq1d
    @91
    @92
    @92
    @7
    @1
    wss
    #
    wa
    @12
    @91
    @93
    @92
    @90
    @6
    cU
    wss
    #
    @0
    @93
    @5
    @90
    @6
    cU
    @10
    @9
    @6
    @9
    cfn
    inss1
    sseli
    elpwid
    wph
    @0
    @3
    simprl
    @94
    @0
    wa
    @6
    cJ
    @6
    cU
    cJ
    sstr
    unissd
    syl2anr
    biantrud
    @1
    @7
    eqss
    syl6bbr
    bitrd
    rexbidva
    mpbid
end
