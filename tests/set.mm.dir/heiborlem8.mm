include "cv.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "cxmt.mm"
include "wcel.mm"
include "cms.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "sseldd.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "wa.mm"
include "c2nd.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cn.mm"
include "rphalfcl.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "heiborlem7.mm"
include "vtoclri.mm"
include "syl.mm"
include "adantl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "heiborlem4.mm"
include "fvex.mm"
include "vex.mm"
include "heiborlem2.mm"
include "simp3bi.mm"
include "sylan2.mm"
include "ad2ant2r.mm"
include "wi.mm"
include "c1st.mm"
include "c1.mm"
include "cexp.mm"
include "cxr.mm"
include "cle.mm"
include "ad2antrr.mm"
include "cxp.mm"
include "heiborlem5.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "ad2antrl.mm"
include "rpxrd.mm"
include "xp2nd.mm"
include "c3.mm"
include "1le3.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "elrp.mm"
include "1re.mm"
include "3re.mm"
include "lediv1.mm"
include "mp3an12.mm"
include "sylbi.mm"
include "mpbii.mm"
include "cop.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "ovex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "oveq1.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "op1st.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "1st2nd2.mm"
include "df-ov.mm"
include "syl6reqr.mm"
include "3sstr3d.mm"
include "ccl.mm"
include "ctop.mm"
include "cuni.mm"
include "mopntop.mm"
include "blssm.mm"
include "mopnuni.mm"
include "eqid.mm"
include "sscls.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "blsscls.mm"
include "syl23anc.mm"
include "eqsstr3d.mm"
include "rpre.mm"
include "ccom.mm"
include "clm.mm"
include "heiborlem6.mm"
include "caublcls.mm"
include "3expia.mm"
include "mpdan.mm"
include "imp.mm"
include "blhalf.mm"
include "syl22anc.mm"
include "sstrd.mm"
include "sstr2.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csn.mm"
include "unisng.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "unieq.mm"
include "rspcev.mm"
include "sylan.mm"
include "syldan.mm"
include "sseq1.mm"
include "notbid.mm"
include "elab2.mm"
include "con2bii.mm"
include "sylib.mm"
include "ex.mm"
include "syld.mm"
include "mt2d.mm"
include "rexlimddv.mm"
include "nrexdv.mm"
include "pm2.21dd.mm"

theorem heiborlem8
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vr: setvar r
  let vg: setvar g
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heibor.4: |- G = { <. y , n >. | ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) }
  assume heibor.5: |- B = ( z e. X , m e. NN0 |-> ( z ( ball ` D ) ( 1 / ( 2 ^ m ) ) ) )
  assume heibor.6: |- ( ph -> D e. ( CMet ` X ) )
  assume heibor.7: |- ( ph -> F : NN0 --> ( ~P X i^i Fin ) )
  assume heibor.8: |- ( ph -> A. n e. NN0 X = U_ y e. ( F ` n ) ( y B n ) )
  assume heibor.9: |- ( ph -> A. x e. G ( ( T ` x ) G ( ( 2nd ` x ) + 1 ) /\ ( ( B ` x ) i^i ( ( T ` x ) B ( ( 2nd ` x ) + 1 ) ) ) e. K ) )
  assume heibor.10: |- ( ph -> C G 0 )
  assume heibor.11: |- S = seq 0 ( T , ( m e. NN0 |-> if ( m = 0 , C , ( m - 1 ) ) ) )
  assume heibor.12: |- M = ( n e. NN |-> <. ( S ` n ) , ( 3 / ( 2 ^ n ) ) >. )
  assume heibor.13: |- ( ph -> U C_ J )
  assume heibor.14: |- Y e. _V
  assume heibor.15: |- ( ph -> Y e. Z )
  assume heibor.16: |- ( ph -> Z e. U )
  assume heibor.17: |- ( ph -> ( 1st o. M ) ( ~~>t ` J ) Y )

  disjoint B x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint n u
  disjoint F n
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint ph x
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint u v
  disjoint u z
  disjoint D u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint D v
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint M m
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B n
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint J m
  disjoint J n
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint U n
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint ps y
  disjoint ps z
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C n
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint Y x
  disjoint Z v
  disjoint Z x
  disjoint n t
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
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
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint g r
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph t
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
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint M g
  disjoint M k
  disjoint M r
  disjoint M t
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J k
  disjoint J r
  disjoint J t
  disjoint U g
  disjoint U t
  disjoint g ps
  disjoint ps t
  disjoint S k
  disjoint S t
  disjoint X g
  disjoint X k
  disjoint X r
  disjoint X t
  disjoint C t
  disjoint K g
  disjoint K t
  disjoint Y k
  disjoint Y t
  disjoint Z k
  assert |- ( ph -> ps )

  proof
    wph
    cY
    vx
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    cZ
    wss
    #
    vx
    crp
    wrex
    #
    wps
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cZ
    cJ
    wcel
    cY
    cZ
    wcel
    @4
    wph
    cD
    cX
    cms
    cfv
    wcel
    cD
    cX
    cme
    cfv
    wcel
    @5
    heibor.6
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    #
    wph
    cU
    cJ
    cZ
    heibor.13
    heibor.16
    sseldd
    heibor.15
    vx
    cZ
    cD
    cY
    cJ
    cX
    heibor.1
    mopni2
    syl3anc
    wph
    @3
    vx
    crp
    wph
    @0
    crp
    wcel
    #
    wa
    #
    vk
    cv
    #
    cM
    cfv
    #
    c2nd
    cfv
    #
    @0
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @3
    wn
    vk
    cn
    @7
    @13
    vk
    cn
    wrex
    #
    wph
    @7
    @12
    crp
    wcel
    #
    @14
    @0
    rphalfcl
    #
    @11
    vr
    cv
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    @14
    vr
    @12
    crp
    @17
    @12
    wceq
    @18
    @13
    vk
    cn
    @17
    @12
    @11
    clt
    breq2
    rexbidv
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vk
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    vr
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem7
    vtoclri
    syl
    adantl
    @8
    @9
    cn
    wcel
    #
    @13
    wa
    #
    wa
    #
    @3
    @9
    cS
    cfv
    #
    @9
    cB
    co
    #
    cK
    wcel
    #
    wph
    @19
    @24
    @7
    @13
    @19
    wph
    @9
    cn0
    wcel
    #
    @24
    @9
    nnnn0
    #
    wph
    @25
    wa
    @22
    @9
    cG
    wbr
    #
    @24
    wph
    vx
    vy
    vz
    vv
    vu
    @9
    cB
    cC
    cD
    cS
    cT
    cU
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
    heibor.9
    heibor.10
    heibor.11
    heiborlem4
    @27
    @25
    @22
    @9
    cF
    cfv
    wcel
    @24
    vy
    vv
    vu
    @22
    cB
    @9
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
    @9
    cS
    fvex
    #
    vk
    vex
    heiborlem2
    simp3bi
    syl
    sylan2
    ad2ant2r
    @21
    @3
    @23
    cZ
    wss
    #
    @24
    wn
    #
    @21
    @23
    @2
    wss
    @3
    @29
    wi
    @21
    @23
    @10
    @1
    cfv
    #
    @2
    @21
    @10
    c1st
    cfv
    #
    c1
    c2
    @9
    cexp
    co
    #
    cdiv
    co
    #
    @1
    co
    #
    @32
    @11
    @1
    co
    #
    @23
    @31
    @21
    @5
    @32
    cX
    wcel
    #
    @34
    cxr
    wcel
    @11
    cxr
    wcel
    #
    @34
    @11
    cle
    wbr
    @35
    @36
    wss
    wph
    @5
    @7
    @20
    @6
    ad2antrr
    #
    @21
    @10
    cX
    crp
    cxp
    #
    wcel
    #
    @37
    wph
    @19
    @41
    @7
    @13
    wph
    cn
    @40
    @9
    cM
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem5
    #
    ffvelrnda
    ad2ant2r
    #
    @10
    cX
    crp
    xp1st
    syl
    #
    @21
    @34
    @19
    @34
    crp
    wcel
    @8
    @13
    @19
    @33
    @19
    @33
    @19
    c2
    cn
    wcel
    @25
    @33
    cn
    wcel
    2nn
    @26
    c2
    @9
    nnexpcl
    sylancr
    nnrpd
    #
    rpreccld
    ad2antrl
    rpxrd
    @21
    @11
    @21
    @41
    @11
    crp
    wcel
    @43
    @10
    cX
    crp
    xp2nd
    syl
    rpxrd
    #
    @21
    @34
    c3
    @33
    cdiv
    co
    #
    @11
    cle
    @19
    @34
    @47
    cle
    wbr
    #
    @8
    @13
    @19
    @33
    crp
    wcel
    #
    @48
    @45
    @49
    c1
    c3
    cle
    wbr
    #
    @48
    1le3
    @49
    @33
    cr
    wcel
    cc0
    @33
    clt
    wbr
    wa
    #
    @50
    @48
    wb
    #
    @33
    elrp
    c1
    cr
    wcel
    c3
    cr
    wcel
    @51
    @52
    1re
    3re
    c1
    c3
    @33
    lediv1
    mp3an12
    sylbi
    mpbii
    syl
    ad2antrl
    @19
    @11
    @47
    wceq
    @8
    @13
    @19
    @11
    @22
    @47
    cop
    #
    c2nd
    cfv
    @47
    @19
    @10
    @53
    c2nd
    vn
    @9
    vn
    cv
    #
    cS
    cfv
    #
    c3
    c2
    @54
    cexp
    co
    #
    cdiv
    co
    #
    cop
    @53
    cn
    cM
    vn
    vk
    weq
    #
    @55
    @22
    @57
    @47
    @54
    @9
    cS
    fveq2
    @58
    @56
    @33
    c3
    cdiv
    @54
    @9
    c2
    cexp
    oveq2
    oveq2d
    opeq12d
    heibor.12
    @22
    @47
    opex
    fvmpt
    #
    fveq2d
    @22
    @47
    @28
    c3
    @33
    cdiv
    ovex
    #
    op2nd
    syl6eq
    ad2antrl
    breqtrrd
    cD
    @32
    @34
    @11
    cX
    ssbl
    syl221anc
    @21
    @32
    @9
    cB
    co
    #
    @35
    @23
    @21
    @37
    @25
    @61
    @35
    wceq
    @44
    @19
    @25
    @8
    @13
    @26
    ad2antrl
    vz
    vm
    @32
    @9
    cX
    cn0
    vz
    cv
    #
    c1
    c2
    vm
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @1
    co
    @35
    cB
    @32
    @65
    @1
    co
    @62
    @32
    @65
    @1
    oveq1
    vm
    vk
    weq
    #
    @65
    @34
    @32
    @1
    @66
    @64
    @33
    c1
    cdiv
    @63
    @9
    c2
    cexp
    oveq2
    oveq2d
    oveq2d
    heibor.5
    @32
    @34
    @1
    ovex
    ovmpt2
    syl2anc
    @21
    @32
    @22
    @9
    cB
    @19
    @32
    @22
    wceq
    @8
    @13
    @19
    @32
    @53
    c1st
    cfv
    @22
    @19
    @10
    @53
    c1st
    @59
    fveq2d
    @22
    @47
    @28
    @60
    op1st
    syl6eq
    ad2antrl
    oveq1d
    eqtr3d
    @21
    @31
    @32
    @11
    cop
    #
    @1
    cfv
    @36
    @21
    @10
    @67
    @1
    @21
    @41
    @10
    @67
    wceq
    @43
    @10
    cX
    crp
    1st2nd2
    syl
    fveq2d
    @32
    @11
    @1
    df-ov
    syl6reqr
    #
    3sstr3d
    @21
    @31
    @31
    cJ
    ccl
    cfv
    #
    cfv
    #
    @2
    @21
    cJ
    ctop
    wcel
    #
    @31
    cJ
    cuni
    #
    wss
    @31
    @70
    wss
    @21
    @5
    @71
    @39
    cD
    cJ
    cX
    heibor.1
    mopntop
    syl
    @21
    @36
    cX
    @31
    @72
    @21
    @5
    @37
    @38
    @36
    cX
    wss
    @39
    @44
    @46
    cD
    @32
    @11
    cX
    blssm
    syl3anc
    @68
    @21
    @5
    cX
    @72
    wceq
    @39
    cD
    cJ
    cX
    heibor.1
    mopnuni
    syl
    3sstr3d
    @31
    cJ
    @72
    @72
    eqid
    sscls
    syl2anc
    @21
    @70
    @32
    @12
    @1
    co
    #
    @2
    @21
    @70
    @36
    @69
    cfv
    #
    @73
    @21
    @36
    @31
    @69
    @68
    fveq2d
    @21
    @5
    @37
    @38
    @12
    cxr
    wcel
    @13
    @74
    @73
    wss
    @39
    @44
    @46
    @21
    @12
    @7
    @15
    wph
    @20
    @16
    ad2antlr
    rpxrd
    @8
    @19
    @13
    simprr
    cD
    @32
    @11
    @12
    cJ
    cX
    heibor.1
    blsscls
    syl23anc
    eqsstr3d
    #
    @21
    @5
    @37
    @0
    cr
    wcel
    #
    cY
    @73
    wcel
    @73
    @2
    wss
    @39
    @44
    @7
    @76
    wph
    @20
    @0
    rpre
    ad2antlr
    @21
    @70
    @73
    cY
    @75
    wph
    @19
    cY
    @70
    wcel
    #
    @7
    @13
    wph
    @19
    @77
    wph
    c1st
    cM
    ccom
    cY
    cJ
    clm
    cfv
    wbr
    #
    @19
    @77
    wi
    heibor.17
    wph
    @78
    @19
    @77
    wph
    @9
    cD
    cY
    vt
    cM
    cJ
    cX
    @6
    @42
    wph
    vx
    vy
    vz
    vv
    vu
    cB
    cC
    cD
    cS
    cT
    cU
    vt
    vm
    vn
    cF
    cG
    cJ
    cK
    cM
    cX
    heibor.1
    heibor.3
    heibor.4
    heibor.5
    heibor.6
    heibor.7
    heibor.8
    heibor.9
    heibor.10
    heibor.11
    heibor.12
    heiborlem6
    heibor.1
    caublcls
    3expia
    mpdan
    imp
    ad2ant2r
    sseldd
    @0
    cD
    cX
    @32
    cY
    blhalf
    syl22anc
    sstrd
    sstrd
    sstrd
    @23
    @2
    cZ
    sstr2
    syl
    wph
    @29
    @30
    wi
    @7
    @20
    wph
    @29
    @30
    wph
    @29
    wa
    @23
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
    @30
    wph
    @29
    @23
    cZ
    csn
    #
    cuni
    #
    wss
    #
    @84
    wph
    @87
    @29
    wph
    @86
    cZ
    @23
    wph
    cZ
    cU
    wcel
    @86
    cZ
    wceq
    heibor.16
    cZ
    cU
    unisng
    syl
    sseq2d
    biimpar
    wph
    @85
    @83
    wcel
    @87
    @84
    wph
    @82
    cfn
    @85
    wph
    @85
    cU
    wss
    @85
    @82
    wcel
    wph
    cZ
    cU
    heibor.16
    snssd
    @85
    cU
    cZ
    snex
    elpw
    sylibr
    @85
    cfn
    wcel
    wph
    cZ
    snfi
    a1i
    elind
    @81
    @87
    vv
    @85
    @83
    @79
    @85
    wceq
    @80
    @86
    @23
    @79
    @85
    unieq
    sseq2d
    rspcev
    sylan
    syldan
    @24
    @84
    vu
    cv
    #
    @80
    wss
    #
    vv
    @83
    wrex
    #
    wn
    @84
    wn
    vu
    @23
    cK
    @22
    @9
    cB
    ovex
    @88
    @23
    wceq
    #
    @90
    @84
    @91
    @89
    @81
    vv
    @83
    @88
    @23
    @80
    sseq1
    rexbidv
    notbid
    heibor.3
    elab2
    con2bii
    sylib
    ex
    ad2antrr
    syld
    mt2d
    rexlimddv
    nrexdv
    pm2.21dd
end
