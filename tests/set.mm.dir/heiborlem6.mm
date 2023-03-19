include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cbl.mm"
include "wss.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c3.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cn0.mm"
include "nnnn0.mm"
include "cxmt.mm"
include "cr.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cme.mm"
include "cms.mm"
include "cmetmet.mm"
include "syl.mm"
include "metxmet.mm"
include "adantr.mm"
include "cpw.mm"
include "wf.mm"
include "cfn.mm"
include "cin.mm"
include "inss1.mm"
include "fss.mm"
include "sylancl.mm"
include "peano2nn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elpwid.mm"
include "heiborlem4.mm"
include "sylan2.mm"
include "fvex.mm"
include "ovex.mm"
include "heiborlem2.mm"
include "simp2bi.mm"
include "sseldd.mm"
include "ffvelrnda.mm"
include "vex.mm"
include "crp.mm"
include "3re.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "adantl.mm"
include "rerpdivcl.mm"
include "mpan.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "oveq1.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovmpt2.mm"
include "sylancom.mm"
include "wi.mm"
include "cop.mm"
include "df-br.mm"
include "c2nd.mm"
include "wral.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "op2ndd.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq12d.mm"
include "ineq12d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspccv.mm"
include "syl5bi.mm"
include "mpd.mm"
include "simpld.mm"
include "syl2anc.mm"
include "simprd.mm"
include "cuni.mm"
include "wrex.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "0ss.mm"
include "unieq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "0ex.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "elab2.mm"
include "con2bii.mm"
include "mpbi.mm"
include "nelne2.mm"
include "eqnetrrd.mm"
include "cxad.mm"
include "rpreccld.mm"
include "rpred.mm"
include "rexadd.mm"
include "breq1d.mm"
include "cxr.mm"
include "rpxrd.mm"
include "w3a.mm"
include "bldisj.mm"
include "3exp2.mm"
include "imp32.mm"
include "syl32anc.mm"
include "sylbird.mm"
include "necon3ad.mm"
include "rpaddcld.mm"
include "metcl.mm"
include "syl3anc.mm"
include "letrid.mm"
include "ord.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cuz.mm"
include "seqp1.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "fveq1i.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"
include "cvv.mm"
include "nn0p1nn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "syl6eqel.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "metsym.mm"
include "cmul.mm"
include "3cn.mm"
include "2timesi.mm"
include "pncan3oi.mm"
include "df-3.mm"
include "3eqtri.mm"
include "rpcn.mm"
include "rpne0.mm"
include "2cn.mm"
include "mulcli.mm"
include "divsubdir.mm"
include "mp3an12.mm"
include "divdir.mm"
include "3eqtr3a.mm"
include "2cnne0.mm"
include "divcan5.mm"
include "mp3an13.mm"
include "mulcom.mm"
include "expp1.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "2t1e2.mm"
include "a1i.mm"
include "3eqtr4d.mm"
include "3brtr4d.mm"
include "blss2.mm"
include "syl33anc.mm"
include "peano2nn.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "3sstr4d.mm"
include "ralrimiva.mm"

theorem heiborlem6
  let wph: wff ph
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
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let vt: setvar t
  let cA: class A
  let vr: setvar r
  let vg: setvar g
  let wps: wff ps
  let cY: class Y
  let cZ: class Z
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

  disjoint B x
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint k n
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n u
  disjoint F n
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint G k
  disjoint G x
  disjoint k ph
  disjoint ph x
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
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
  disjoint M k
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
  disjoint J k
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
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X k
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
  disjoint n t
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint k r
  disjoint k t
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
  disjoint G t
  disjoint g r
  disjoint g ph
  disjoint ph r
  disjoint ph t
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint m r
  disjoint m t
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint M g
  disjoint M r
  disjoint M t
  disjoint B g
  disjoint B t
  disjoint J g
  disjoint J r
  disjoint J t
  disjoint U g
  disjoint U t
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S t
  disjoint X g
  disjoint X r
  disjoint X t
  disjoint C t
  disjoint K g
  disjoint K t
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( ph -> A. k e. NN ( ( ball ` D ) ` ( M ` ( k + 1 ) ) ) C_ ( ( ball ` D ) ` ( M ` k ) ) )

  proof
    wph
    vk
    cv
    #
    c1
    caddc
    co
    #
    cM
    cfv
    #
    cD
    cbl
    cfv
    #
    cfv
    #
    @0
    cM
    cfv
    #
    @3
    cfv
    #
    wss
    vk
    cn
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @1
    cS
    cfv
    #
    c3
    c2
    @1
    cexp
    co
    #
    cdiv
    co
    #
    @3
    co
    #
    @0
    cS
    cfv
    #
    c3
    c2
    @0
    cexp
    co
    #
    cdiv
    co
    #
    @3
    co
    #
    @4
    @6
    @7
    wph
    @0
    cn0
    wcel
    #
    @12
    @16
    wss
    #
    @0
    nnnn0
    wph
    @17
    wa
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @9
    cX
    wcel
    @13
    cX
    wcel
    #
    @11
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @9
    @13
    cD
    co
    #
    @15
    @11
    cmin
    co
    #
    cle
    wbr
    @18
    wph
    @20
    @17
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @20
    wph
    cD
    cX
    cms
    cfv
    wcel
    @26
    heibor.6
    cD
    cX
    cmetmet
    syl
    #
    cD
    cX
    metxmet
    syl
    adantr
    #
    @19
    @1
    cF
    cfv
    #
    cX
    @9
    @19
    @29
    cX
    wph
    cn0
    cX
    cpw
    #
    cF
    wf
    #
    @1
    cn0
    wcel
    #
    @29
    @30
    wcel
    @17
    wph
    cn0
    @30
    cfn
    cin
    #
    cF
    wf
    @33
    @30
    wss
    @31
    heibor.7
    @30
    cfn
    inss1
    cn0
    @33
    @30
    cF
    fss
    sylancl
    #
    @0
    peano2nn0
    #
    cn0
    @30
    @1
    cF
    ffvelrn
    syl2an
    elpwid
    #
    @19
    @9
    @1
    cG
    wbr
    #
    @9
    @29
    wcel
    #
    @17
    wph
    @32
    @37
    @35
    wph
    vx
    vy
    vz
    vv
    vu
    @1
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
    sylan2
    @37
    @32
    @38
    @9
    @1
    cB
    co
    cK
    wcel
    vy
    vv
    vu
    @9
    cB
    @1
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
    @1
    cS
    fvex
    @0
    c1
    caddc
    ovex
    #
    heiborlem2
    simp2bi
    syl
    sseldd
    @19
    @0
    cF
    cfv
    #
    cX
    @13
    @19
    @40
    cX
    wph
    cn0
    @30
    @0
    cF
    @34
    ffvelrnda
    elpwid
    @19
    @13
    @0
    cG
    wbr
    #
    @13
    @40
    wcel
    #
    wph
    vx
    vy
    vz
    vv
    vu
    @0
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
    #
    @41
    @17
    @42
    @13
    @0
    cB
    co
    #
    cK
    wcel
    vy
    vv
    vu
    @13
    cB
    @0
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
    @0
    cS
    fvex
    #
    vk
    vex
    #
    heiborlem2
    simp2bi
    syl
    sseldd
    #
    @19
    c3
    cr
    wcel
    #
    @10
    crp
    wcel
    #
    @22
    3re
    @17
    @49
    wph
    @17
    @10
    @17
    c2
    cn
    wcel
    #
    @32
    @10
    cn
    wcel
    2nn
    @35
    c2
    @1
    nnexpcl
    sylancr
    nnrpd
    #
    adantl
    c3
    @10
    rerpdivcl
    sylancr
    @19
    @48
    @14
    crp
    wcel
    #
    @23
    3re
    @17
    @52
    wph
    @17
    @14
    @50
    @17
    @14
    cn
    wcel
    2nn
    c2
    @0
    nnexpcl
    mpan
    nnrpd
    #
    adantl
    c3
    @14
    rerpdivcl
    sylancr
    @19
    @13
    @13
    @0
    cT
    co
    #
    cD
    co
    #
    c1
    @14
    cdiv
    co
    #
    c1
    @10
    cdiv
    co
    #
    caddc
    co
    #
    @24
    @25
    cle
    @19
    @58
    @55
    cle
    wbr
    #
    wn
    #
    @55
    @58
    cle
    wbr
    #
    @19
    @13
    @56
    @3
    co
    #
    @54
    @57
    @3
    co
    #
    cin
    #
    c0
    wne
    @60
    @19
    @44
    @54
    @1
    cB
    co
    #
    cin
    #
    @64
    c0
    @19
    @44
    @62
    @65
    @63
    wph
    @17
    @21
    @44
    @62
    wceq
    @47
    vz
    vm
    @13
    @0
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
    @3
    co
    #
    @62
    cB
    @13
    @70
    @3
    co
    @67
    @13
    @70
    @3
    oveq1
    vm
    vk
    weq
    #
    @70
    @56
    @13
    @3
    @72
    @69
    @14
    c1
    cdiv
    @68
    @0
    c2
    cexp
    oveq2
    oveq2d
    oveq2d
    heibor.5
    @13
    @56
    @3
    ovex
    ovmpt2
    sylancom
    @19
    @54
    cX
    wcel
    #
    @32
    @65
    @63
    wceq
    @19
    @29
    cX
    @54
    @36
    @19
    @54
    @1
    cG
    wbr
    #
    @54
    @29
    wcel
    #
    @19
    @74
    @66
    cK
    wcel
    #
    @19
    @41
    @74
    @76
    wa
    #
    @43
    wph
    @41
    @77
    wi
    @17
    @41
    @13
    @0
    cop
    #
    cG
    wcel
    #
    wph
    @77
    @13
    @0
    cG
    df-br
    wph
    vx
    cv
    #
    cT
    cfv
    #
    @80
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
    @80
    cB
    cfv
    #
    @81
    @83
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
    @79
    @77
    wi
    heibor.9
    @89
    @77
    vx
    @78
    cG
    @80
    @78
    wceq
    #
    @84
    @74
    @88
    @76
    @90
    @81
    @54
    @83
    @1
    cG
    @90
    @81
    @78
    cT
    cfv
    @54
    @80
    @78
    cT
    fveq2
    @13
    @0
    cT
    df-ov
    syl6eqr
    #
    @90
    @82
    @0
    c1
    caddc
    @13
    @0
    @80
    @45
    @46
    op2ndd
    oveq1d
    #
    breq12d
    @90
    @87
    @66
    cK
    @90
    @85
    @44
    @86
    @65
    @90
    @85
    @78
    cB
    cfv
    @44
    @80
    @78
    cB
    fveq2
    @13
    @0
    cB
    df-ov
    syl6eqr
    @90
    @81
    @54
    @83
    @1
    cB
    @91
    @92
    oveq12d
    ineq12d
    eleq1d
    anbi12d
    rspccv
    syl
    syl5bi
    adantr
    mpd
    #
    simpld
    @74
    @32
    @75
    @65
    cK
    wcel
    vy
    vv
    vu
    @54
    cB
    @1
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
    @13
    @0
    cT
    ovex
    @39
    heiborlem2
    simp2bi
    syl
    sseldd
    #
    @17
    @32
    wph
    @35
    adantl
    vz
    vm
    @54
    @1
    cX
    cn0
    @71
    @63
    cB
    @54
    @70
    @3
    co
    @67
    @54
    @70
    @3
    oveq1
    @68
    @1
    wceq
    #
    @70
    @57
    @54
    @3
    @95
    @69
    @10
    c1
    cdiv
    @68
    @1
    c2
    cexp
    oveq2
    oveq2d
    oveq2d
    heibor.5
    @54
    @57
    @3
    ovex
    ovmpt2
    syl2anc
    ineq12d
    @19
    @76
    c0
    cK
    wcel
    #
    wn
    #
    @66
    c0
    wne
    @19
    @74
    @76
    @93
    simprd
    c0
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
    @97
    c0
    @102
    wcel
    #
    c0
    c0
    cuni
    #
    wss
    #
    @103
    @104
    c0
    @101
    wcel
    c0
    cfn
    wcel
    cU
    0elpw
    0fin
    c0
    @101
    cfn
    elin
    mpbir2an
    @105
    0ss
    @100
    @106
    vv
    c0
    @102
    @98
    c0
    wceq
    @99
    @105
    c0
    @98
    c0
    unieq
    sseq2d
    rspcev
    mp2an
    @96
    @103
    vu
    cv
    #
    @99
    wss
    #
    vv
    @102
    wrex
    #
    wn
    @103
    wn
    vu
    c0
    cK
    0ex
    @107
    c0
    wceq
    #
    @109
    @103
    @110
    @108
    @100
    vv
    @102
    @107
    c0
    @99
    sseq1
    rexbidv
    notbid
    heibor.3
    elab2
    con2bii
    mpbi
    @66
    c0
    cK
    nelne2
    sylancl
    eqnetrrd
    @19
    @59
    @64
    c0
    @19
    @59
    @56
    @57
    cxad
    co
    #
    @55
    cle
    wbr
    #
    @64
    c0
    wceq
    #
    @19
    @111
    @58
    @55
    cle
    @19
    @56
    cr
    wcel
    @57
    cr
    wcel
    @111
    @58
    wceq
    @19
    @56
    @17
    @56
    crp
    wcel
    wph
    @17
    @14
    @53
    rpreccld
    adantl
    #
    rpred
    @19
    @57
    @17
    @57
    crp
    wcel
    wph
    @17
    @10
    @51
    rpreccld
    adantl
    #
    rpred
    @56
    @57
    rexadd
    syl2anc
    breq1d
    @19
    @20
    @21
    @73
    @56
    cxr
    wcel
    #
    @57
    cxr
    wcel
    #
    @112
    @113
    wi
    #
    @28
    @47
    @94
    @19
    @56
    @114
    rpxrd
    @19
    @57
    @115
    rpxrd
    @20
    @21
    @73
    w3a
    #
    @116
    @117
    @118
    @119
    @116
    @117
    @112
    @113
    cD
    @13
    @54
    @56
    @57
    cX
    bldisj
    3exp2
    imp32
    syl32anc
    sylbird
    necon3ad
    mpd
    @19
    @59
    @61
    @19
    @58
    @55
    @19
    @58
    @19
    @56
    @57
    @114
    @115
    rpaddcld
    rpred
    @19
    @26
    @21
    @73
    @55
    cr
    wcel
    wph
    @26
    @17
    @27
    adantr
    #
    @47
    @94
    @13
    @54
    cD
    cX
    metcl
    syl3anc
    letrid
    ord
    mpd
    @19
    @24
    @54
    @13
    cD
    co
    #
    @55
    @19
    @9
    @54
    @13
    cD
    @17
    @9
    @54
    wceq
    wph
    @17
    @9
    @13
    @1
    vm
    cn0
    @68
    cc0
    wceq
    #
    cC
    @68
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cT
    co
    #
    @54
    @17
    @1
    cT
    @125
    cc0
    cseq
    #
    cfv
    #
    @0
    @128
    cfv
    #
    @126
    cT
    co
    #
    @9
    @127
    @129
    @131
    wceq
    @0
    cc0
    cuz
    cfv
    cn0
    cT
    @125
    cc0
    @0
    seqp1
    nn0uz
    eleq2s
    @1
    cS
    @128
    heibor.11
    fveq1i
    @13
    @130
    @126
    cT
    @0
    cS
    @128
    heibor.11
    fveq1i
    oveq1i
    3eqtr4g
    @17
    @126
    @0
    @13
    cT
    @17
    @126
    @1
    cc0
    wceq
    #
    cC
    @1
    c1
    cmin
    co
    #
    cif
    #
    @133
    @0
    @17
    @32
    @134
    cvv
    wcel
    @126
    @134
    wceq
    @35
    @17
    @134
    @133
    cvv
    @17
    @132
    cC
    @133
    @17
    @1
    cn
    wcel
    #
    @132
    wn
    @0
    nn0p1nn
    @135
    @1
    cc0
    @1
    nnne0
    neneqd
    syl
    iffalsed
    #
    @1
    c1
    cmin
    ovex
    syl6eqel
    vm
    @1
    @124
    @134
    cn0
    cvv
    @125
    @95
    @122
    @132
    @123
    @133
    cC
    @68
    @1
    cc0
    eqeq1
    @68
    @1
    c1
    cmin
    oveq1
    ifbieq2d
    @125
    eqid
    fvmptg
    syl2anc
    @136
    @17
    @0
    cc
    wcel
    c1
    cc
    wcel
    #
    @133
    @0
    wceq
    @0
    nn0cn
    ax-1cn
    @0
    c1
    pncan
    sylancl
    3eqtrd
    oveq2d
    eqtrd
    adantl
    oveq1d
    @19
    @26
    @73
    @21
    @121
    @55
    wceq
    @120
    @94
    @47
    @54
    @13
    cD
    cX
    metsym
    syl3anc
    eqtrd
    @17
    @25
    @58
    wceq
    wph
    @17
    c2
    c3
    cmul
    co
    #
    @10
    cdiv
    co
    #
    @11
    cmin
    co
    #
    c2
    @10
    cdiv
    co
    #
    @57
    caddc
    co
    #
    @25
    @58
    @17
    @138
    c3
    cmin
    co
    #
    @10
    cdiv
    co
    #
    c2
    c1
    caddc
    co
    #
    @10
    cdiv
    co
    #
    @140
    @142
    @143
    @145
    @10
    cdiv
    @143
    c3
    c3
    caddc
    co
    #
    c3
    cmin
    co
    c3
    @145
    @138
    @147
    c3
    cmin
    c3
    3cn
    2timesi
    oveq1i
    c3
    c3
    3cn
    3cn
    pncan3oi
    df-3
    3eqtri
    oveq1i
    @17
    @49
    @144
    @140
    wceq
    #
    @51
    @49
    @10
    cc
    wcel
    #
    @10
    cc0
    wne
    #
    @148
    @10
    rpcn
    #
    @10
    rpne0
    #
    @138
    cc
    wcel
    c3
    cc
    wcel
    #
    @149
    @150
    wa
    #
    @148
    c2
    c3
    2cn
    3cn
    mulcli
    3cn
    @138
    c3
    @10
    divsubdir
    mp3an12
    syl2anc
    syl
    @17
    @49
    @146
    @142
    wceq
    #
    @51
    @49
    @149
    @150
    @155
    @151
    @152
    c2
    cc
    wcel
    #
    @137
    @154
    @155
    2cn
    ax-1cn
    c2
    c1
    @10
    divdir
    mp3an12
    syl2anc
    syl
    3eqtr3a
    @17
    @15
    @139
    @11
    cmin
    @17
    @138
    c2
    @14
    cmul
    co
    #
    cdiv
    co
    #
    @15
    @139
    @17
    @52
    @158
    @15
    wceq
    #
    @53
    @52
    @14
    cc
    wcel
    #
    @14
    cc0
    wne
    #
    @159
    @14
    rpcn
    #
    @14
    rpne0
    #
    @153
    @160
    @161
    wa
    #
    @156
    c2
    cc0
    wne
    wa
    #
    @159
    3cn
    2cnne0
    c3
    @14
    c2
    divcan5
    mp3an13
    syl2anc
    syl
    @17
    @157
    @10
    @138
    cdiv
    @17
    @157
    @14
    c2
    cmul
    co
    #
    @10
    @17
    @156
    @160
    @157
    @166
    wceq
    2cn
    @17
    @52
    @160
    @53
    @162
    syl
    c2
    @14
    mulcom
    sylancr
    @156
    @17
    @10
    @166
    wceq
    2cn
    c2
    @0
    expp1
    mpan
    eqtr4d
    #
    oveq2d
    eqtr3d
    oveq1d
    @17
    @56
    @141
    @57
    caddc
    @17
    c2
    c1
    cmul
    co
    #
    @157
    cdiv
    co
    #
    @56
    @141
    @17
    @52
    @169
    @56
    wceq
    #
    @53
    @52
    @160
    @161
    @170
    @162
    @163
    @137
    @164
    @165
    @170
    ax-1cn
    2cnne0
    c1
    @14
    c2
    divcan5
    mp3an13
    syl2anc
    syl
    @17
    @168
    c2
    @157
    @10
    cdiv
    @168
    c2
    wceq
    @17
    2t1e2
    a1i
    @167
    oveq12d
    eqtr3d
    oveq1d
    3eqtr4d
    adantl
    3brtr4d
    cD
    @9
    @13
    @11
    @15
    cX
    blss2
    syl33anc
    sylan2
    @8
    @4
    @9
    @11
    cop
    #
    @3
    cfv
    @12
    @8
    @2
    @171
    @3
    @7
    @2
    @171
    wceq
    #
    wph
    @7
    @135
    @172
    @0
    peano2nn
    vn
    @1
    vn
    cv
    #
    cS
    cfv
    #
    c3
    c2
    @173
    cexp
    co
    #
    cdiv
    co
    #
    cop
    #
    @171
    cn
    cM
    @173
    @1
    wceq
    #
    @174
    @9
    @176
    @11
    @173
    @1
    cS
    fveq2
    @178
    @175
    @10
    c3
    cdiv
    @173
    @1
    c2
    cexp
    oveq2
    oveq2d
    opeq12d
    heibor.12
    @9
    @11
    opex
    fvmpt
    syl
    adantl
    fveq2d
    @9
    @11
    @3
    df-ov
    syl6eqr
    @7
    @6
    @16
    wceq
    wph
    @7
    @6
    @13
    @15
    cop
    #
    @3
    cfv
    @16
    @7
    @5
    @179
    @3
    vn
    @0
    @177
    @179
    cn
    cM
    vn
    vk
    weq
    #
    @174
    @13
    @176
    @15
    @173
    @0
    cS
    fveq2
    @180
    @175
    @14
    c3
    cdiv
    @173
    @0
    c2
    cexp
    oveq2
    oveq2d
    opeq12d
    heibor.12
    @13
    @15
    opex
    fvmpt
    fveq2d
    @13
    @15
    @3
    df-ov
    syl6eqr
    adantl
    3sstr4d
    ralrimiva
end
