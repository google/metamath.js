include "cv.mm"
include "cn.mm"
include "wfn.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ciun.mm"
include "covoln.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "fvex.mm"
include "nnenom.mm"
include "axcc3.mm"
include "simprl.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rspa.mm"
include "adantll.mm"
include "cfn.mm"
include "adantr.mm"
include "cr.mm"
include "cmap.mm"
include "cpw.mm"
include "wss.mm"
include "wf.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "elpwi.mm"
include "syl.mm"
include "crp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "2nn.mm"
include "a1i.mm"
include "id.mm"
include "nnexpcl.mm"
include "syl2anc.mm"
include "nnrp.mm"
include "adantl.mm"
include "rpdivcld.mm"
include "ovncvrrp.mm"
include "n0.mm"
include "sylibr.mm"
include "mpd.mm"
include "ex.mm"
include "adantlr.mm"
include "ralrimi.mm"
include "adantrl.mm"
include "jca.mm"
include "eximdv.mm"
include "mpi.mm"
include "simpl.mm"
include "simprr.mm"
include "w3a.mm"
include "cxp.mm"
include "wf1o.mm"
include "nnf1oxpnn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "fveq12d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "biimpri.mm"
include "3ad2ant3.mm"
include "c2nd.mm"
include "c1st.mm"
include "3ad2antl1.mm"
include "cico.mm"
include "ccom.mm"
include "cvol.mm"
include "cprod.mm"
include "coeq2.mm"
include "fveq1d.mm"
include "prodeq2ad.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "biimpi.mm"
include "ad2antrr.mm"
include "ovnsubaddlem1.mm"
include "syl31anc.mm"
include "exlimdv.mm"
include "syl3anc.mm"

theorem ovnsubaddlem2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cD: class D
  let ve: setvar e
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cL: class L
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vl: setvar l
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vq: setvar q
  let vx: setvar x
  assume ovnsubaddlem2.x: |- ( ph -> X e. Fin )
  assume ovnsubaddlem2.n0: |- ( ph -> X =/= (/) )
  assume ovnsubaddlem2.a: |- ( ph -> A : NN --> ~P ( RR ^m X ) )
  assume ovnsubaddlem2.e: |- ( ph -> E e. RR+ )
  assume ovnsubaddlem2.z: |- Z = ( a e. ~P ( RR ^m X ) |-> { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ( a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) ) } )
  assume ovnsubaddlem2.c: |- C = ( a e. ~P ( RR ^m X ) |-> { l e. ( ( ( RR X. RR ) ^m X ) ^m NN ) | a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( l ` j ) ) ` k ) } )
  assume ovnsubaddlem2.l: |- L = ( h e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. h ) ` k ) ) )
  assume ovnsubaddlem2.d: |- D = ( a e. ~P ( RR ^m X ) |-> ( e e. RR+ |-> { i e. ( C ` a ) | ( sum^ ` ( j e. NN |-> ( L ` ( i ` j ) ) ) ) <_ ( ( ( voln* ` X ) ` a ) +e e ) } ) )

  disjoint A a
  disjoint A e
  disjoint A i
  disjoint A j
  disjoint A n
  disjoint a e
  disjoint a i
  disjoint a j
  disjoint a n
  disjoint e i
  disjoint e j
  disjoint e n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint A k
  disjoint A l
  disjoint a k
  disjoint a l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint k n
  disjoint l n
  disjoint A z
  disjoint a z
  disjoint i z
  disjoint j z
  disjoint k z
  disjoint n z
  disjoint C a
  disjoint C e
  disjoint C i
  disjoint D a
  disjoint D e
  disjoint D i
  disjoint D j
  disjoint D n
  disjoint D k
  disjoint E a
  disjoint E e
  disjoint E i
  disjoint E j
  disjoint E n
  disjoint E k
  disjoint L a
  disjoint L e
  disjoint L i
  disjoint L j
  disjoint L n
  disjoint X a
  disjoint X e
  disjoint X i
  disjoint X j
  disjoint X n
  disjoint X h
  disjoint X k
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint X l
  disjoint X z
  disjoint a ph
  disjoint e ph
  disjoint i ph
  disjoint j ph
  disjoint n ph
  disjoint k ph
  disjoint A f
  disjoint A g
  disjoint A m
  disjoint A q
  disjoint a f
  disjoint a g
  disjoint a m
  disjoint a q
  disjoint e f
  disjoint e g
  disjoint e m
  disjoint e q
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f q
  disjoint g i
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g q
  disjoint i m
  disjoint i q
  disjoint j m
  disjoint j q
  disjoint m n
  disjoint m q
  disjoint n q
  disjoint f k
  disjoint f l
  disjoint g k
  disjoint g l
  disjoint k m
  disjoint l m
  disjoint D f
  disjoint D g
  disjoint D m
  disjoint D q
  disjoint k q
  disjoint E f
  disjoint E g
  disjoint E m
  disjoint E q
  disjoint L m
  disjoint X f
  disjoint X g
  disjoint X m
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint k x
  assert |- ( ph -> ( ( voln* ` X ) ` U_ n e. NN ( A ` n ) ) <_ ( ( sum^ ` ( n e. NN |-> ( ( voln* ` X ) ` ( A ` n ) ) ) ) +e E ) )

  proof
    wph
    vg
    cv
    #
    cn
    wfn
    #
    vn
    cv
    #
    @0
    cfv
    #
    cE
    c2
    @2
    cexp
    co
    #
    cdiv
    co
    #
    @2
    cA
    cfv
    #
    cD
    cfv
    #
    cfv
    #
    wcel
    #
    vn
    cn
    wral
    #
    wa
    #
    vg
    wex
    #
    vn
    cn
    @6
    ciun
    cX
    covoln
    cfv
    #
    cfv
    vn
    cn
    @6
    @13
    cfv
    cmpt
    csumge0
    cfv
    cE
    cxad
    co
    cle
    wbr
    #
    wph
    @1
    @8
    c0
    wne
    #
    @9
    wi
    #
    vn
    cn
    wral
    #
    wa
    #
    vg
    wex
    @12
    vg
    vn
    @8
    cn
    @5
    @7
    fvex
    nnenom
    axcc3
    wph
    @18
    @11
    vg
    wph
    @18
    @11
    wph
    @18
    wa
    @1
    @10
    wph
    @1
    @17
    simprl
    wph
    @17
    @10
    @1
    wph
    @17
    wa
    #
    @9
    vn
    cn
    wph
    @17
    vn
    wph
    vn
    nfv
    @16
    vn
    cn
    nfra1
    nfan
    @19
    @2
    cn
    wcel
    #
    @9
    @19
    @20
    wa
    @16
    @9
    @17
    @20
    @16
    wph
    @16
    vn
    cn
    rspa
    adantll
    wph
    @20
    @16
    @9
    wi
    @17
    wph
    @20
    wa
    #
    @16
    @9
    @21
    @16
    wa
    @15
    @9
    @21
    @15
    @16
    @21
    vi
    cv
    #
    @8
    wcel
    vi
    wex
    @15
    @21
    @6
    cC
    cD
    ve
    vh
    vi
    vj
    vk
    @5
    cL
    cX
    va
    vl
    wph
    cX
    cfn
    wcel
    #
    @20
    ovnsubaddlem2.x
    adantr
    wph
    cX
    c0
    wne
    #
    @20
    ovnsubaddlem2.n0
    adantr
    @21
    @6
    cr
    cX
    cmap
    co
    #
    cpw
    #
    wcel
    @6
    @25
    wss
    @21
    cn
    @26
    @2
    cA
    wph
    cn
    @26
    cA
    wf
    #
    @20
    ovnsubaddlem2.a
    adantr
    wph
    @20
    simpr
    ffvelrnd
    @6
    @25
    elpwi
    syl
    @21
    cE
    @4
    wph
    cE
    crp
    wcel
    #
    @20
    ovnsubaddlem2.e
    adantr
    @20
    @4
    crp
    wcel
    #
    wph
    @20
    @2
    cn0
    wcel
    #
    @29
    @2
    nnnn0
    @30
    @4
    cn
    wcel
    #
    @29
    @30
    c2
    cn
    wcel
    #
    @30
    @31
    @32
    @30
    2nn
    a1i
    @30
    id
    c2
    @2
    nnexpcl
    syl2anc
    @4
    nnrp
    syl
    syl
    adantl
    rpdivcld
    ovnsubaddlem2.c
    ovnsubaddlem2.l
    ovnsubaddlem2.d
    ovncvrrp
    vi
    @8
    n0
    sylibr
    adantr
    @21
    @16
    simpr
    mpd
    ex
    adantlr
    mpd
    ex
    ralrimi
    adantrl
    jca
    ex
    eximdv
    mpi
    wph
    @11
    @14
    vg
    wph
    @11
    @14
    wph
    @11
    wa
    wph
    @1
    @10
    @14
    wph
    @11
    simpl
    wph
    @1
    @10
    simprl
    wph
    @1
    @10
    simprr
    wph
    @1
    @10
    w3a
    #
    cn
    cn
    cn
    cxp
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @14
    vf
    nnf1oxpnn
    @33
    @35
    @14
    vf
    @33
    @35
    @14
    @33
    @35
    wa
    wph
    @1
    vq
    cv
    #
    @0
    cfv
    #
    cE
    c2
    @36
    cexp
    co
    #
    cdiv
    co
    #
    @36
    cA
    cfv
    #
    cD
    cfv
    #
    cfv
    #
    wcel
    #
    vq
    cn
    wral
    #
    @35
    @14
    wph
    @1
    @10
    @35
    simpl1
    wph
    @1
    @10
    @35
    simpl2
    @33
    @44
    @35
    @10
    wph
    @44
    @1
    @44
    @10
    @43
    @9
    vq
    vn
    cn
    @36
    @2
    wceq
    #
    @37
    @3
    @42
    @8
    @36
    @2
    @0
    fveq2
    @45
    @39
    @5
    @41
    @7
    @45
    @40
    @6
    cD
    @36
    @2
    cA
    fveq2
    fveq2d
    @45
    @38
    @4
    cE
    cdiv
    @36
    @2
    c2
    cexp
    oveq2
    oveq2d
    fveq12d
    eleq12d
    cbvralv
    #
    biimpri
    3ad2ant3
    adantr
    @33
    @35
    simpr
    wph
    @1
    @44
    w3a
    #
    @35
    wa
    #
    vz
    cA
    cC
    cD
    ve
    vl
    vi
    vj
    vk
    vm
    vn
    cE
    @34
    vq
    cn
    @36
    @34
    cfv
    #
    c2nd
    cfv
    #
    @49
    c1st
    cfv
    #
    @0
    cfv
    #
    cfv
    #
    cmpt
    @0
    cL
    cX
    cZ
    va
    wph
    @1
    @35
    @23
    @44
    wph
    @23
    @35
    ovnsubaddlem2.x
    adantr
    3ad2antl1
    wph
    @1
    @35
    @24
    @44
    wph
    @24
    @35
    ovnsubaddlem2.n0
    adantr
    3ad2antl1
    wph
    @1
    @35
    @27
    @44
    wph
    @27
    @35
    ovnsubaddlem2.a
    adantr
    3ad2antl1
    wph
    @1
    @35
    @28
    @44
    wph
    @28
    @35
    ovnsubaddlem2.e
    adantr
    3ad2antl1
    ovnsubaddlem2.z
    ovnsubaddlem2.c
    cL
    vh
    cr
    cr
    cxp
    cX
    cmap
    co
    #
    cX
    vk
    cv
    #
    cico
    vh
    cv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    vi
    @54
    cX
    @55
    cico
    @22
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    ovnsubaddlem2.l
    vh
    vi
    @54
    @60
    @64
    @56
    @22
    wceq
    #
    cX
    @59
    @63
    vk
    @65
    @58
    @62
    cvol
    @65
    @55
    @57
    @61
    @56
    @22
    cico
    coeq2
    fveq1d
    fveq2d
    prodeq2ad
    cbvmptv
    eqtri
    ovnsubaddlem2.d
    @48
    @20
    wa
    @10
    @20
    @9
    @47
    @10
    @35
    @20
    @44
    wph
    @10
    @1
    @44
    @10
    @46
    biimpi
    3ad2ant3
    ad2antrr
    @48
    @20
    simpr
    @9
    vn
    cn
    rspa
    syl2anc
    @47
    @35
    simpr
    vq
    vm
    cn
    @53
    vm
    cv
    #
    @34
    cfv
    #
    c2nd
    cfv
    #
    @67
    c1st
    cfv
    #
    @0
    cfv
    #
    cfv
    @36
    @66
    wceq
    #
    @50
    @68
    @52
    @70
    @71
    @51
    @69
    @0
    @71
    @49
    @67
    c1st
    @36
    @66
    @34
    fveq2
    #
    fveq2d
    fveq2d
    @71
    @49
    @67
    c2nd
    @72
    fveq2d
    fveq12d
    cbvmptv
    ovnsubaddlem1
    syl31anc
    ex
    exlimdv
    mpi
    syl3anc
    ex
    exlimdv
    mpd
end
