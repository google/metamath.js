include "cuni.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "uniss.mm"
include "syl.mm"
include "carsguni.mm"
include "sseqtrd.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "c0.mm"
include "com.mm"
include "cdom.mm"
include "cesum.mm"
include "3adant1r.mm"
include "simpr.mm"
include "carsgclctunlem3.mm"
include "cpr.mm"
include "cvv.mm"
include "inex1g.mm"
include "adantl.mm"
include "difexg.mm"
include "prct.mm"
include "syl2anc.mm"
include "elpwincl1.mm"
include "elpwdifcl.mm"
include "prssi.mm"
include "w3a.mm"
include "wi.mm"
include "prex.mm"
include "breq1.mm"
include "sseq1.mm"
include "3anbi23d.mm"
include "unieq.mm"
include "fveq2d.mm"
include "esumeq1.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "mpd3an23.mm"
include "cun.mm"
include "uniprg.mm"
include "inundif.mm"
include "syl6eq.mm"
include "ffvelrnd.mm"
include "wo.mm"
include "ineq2.mm"
include "inidm.mm"
include "inindif.mm"
include "3eqtr3g.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "orcd.mm"
include "ex.mm"
include "esumpr2.mm"
include "3brtr3d.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xaddcld.mm"
include "ffvelrnda.mm"
include "xrletri3.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "elcarsg.mm"
include "mpbir2and.mm"

theorem carsgclctun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let vb: setvar b
  let vf: setvar f
  let cE: class E
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let vg: setvar g
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume carsgsiga.3: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )
  assume carsgclctun.1: |- ( ph -> A ~<_ _om )
  assume carsgclctun.2: |- ( ph -> A C_ ( toCaraSiga ` M ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint E x
  disjoint E y
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  disjoint f k
  disjoint f n
  disjoint f z
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint A g
  disjoint A k
  disjoint A n
  disjoint e g
  disjoint e k
  disjoint e n
  disjoint f g
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint E f
  disjoint E g
  disjoint E k
  disjoint E n
  disjoint M g
  disjoint M k
  disjoint M n
  disjoint O g
  disjoint O n
  disjoint g ph
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> U. A e. ( toCaraSiga ` M ) )

  proof
    wph
    cA
    cuni
    #
    cM
    ccarsg
    cfv
    #
    wcel
    @0
    cO
    wss
    ve
    cv
    #
    @0
    cin
    #
    cM
    cfv
    #
    @2
    @0
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @2
    cM
    cfv
    #
    wceq
    #
    ve
    cO
    cpw
    #
    wral
    wph
    @0
    @1
    cuni
    #
    cO
    wph
    cA
    @1
    wss
    #
    @0
    @11
    wss
    carsgclctun.2
    cA
    @1
    uniss
    syl
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgsiga.1
    carsguni
    sseqtrd
    wph
    @9
    ve
    @10
    wph
    @2
    @10
    wcel
    #
    wa
    #
    @9
    @7
    @8
    cle
    wbr
    #
    @8
    @7
    cle
    wbr
    #
    wa
    #
    @14
    @15
    @16
    @14
    vx
    vy
    cA
    @2
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    @13
    carsgval.1
    adantr
    wph
    @10
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    @13
    carsgval.2
    adantr
    #
    wph
    c0
    cM
    cfv
    #
    cc0
    wceq
    #
    @13
    carsgsiga.1
    adantr
    wph
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @22
    @10
    wss
    #
    @22
    cuni
    #
    cM
    cfv
    #
    @22
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    #
    cle
    wbr
    #
    @13
    carsgsiga.2
    3adant1r
    wph
    @22
    @27
    wss
    @27
    @10
    wcel
    @22
    cM
    cfv
    @28
    cle
    wbr
    @13
    carsgsiga.3
    3adant1r
    wph
    cA
    com
    cdom
    wbr
    @13
    carsgclctun.1
    adantr
    wph
    @12
    @13
    carsgclctun.2
    adantr
    wph
    @13
    simpr
    #
    carsgclctunlem3
    @14
    @3
    @5
    cpr
    #
    cuni
    #
    cM
    cfv
    #
    @32
    @28
    vy
    cesum
    #
    @8
    @7
    cle
    @14
    @32
    com
    cdom
    wbr
    #
    @32
    @10
    wss
    #
    @34
    @35
    cle
    wbr
    #
    @14
    @3
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    @36
    @13
    @39
    wph
    @2
    @0
    @10
    inex1g
    adantl
    @13
    @40
    wph
    @2
    @0
    @10
    difexg
    adantl
    @3
    @5
    cvv
    cvv
    prct
    syl2anc
    @14
    @3
    @10
    wcel
    #
    @5
    @10
    wcel
    #
    @37
    @14
    @2
    @0
    cO
    @31
    elpwincl1
    #
    @14
    @2
    @0
    cO
    @31
    elpwdifcl
    #
    @3
    @5
    @10
    prssi
    syl2anc
    wph
    @36
    @37
    @38
    @13
    @32
    cvv
    wcel
    wph
    @36
    @37
    w3a
    #
    @38
    wi
    #
    @3
    @5
    prex
    wph
    @23
    @24
    w3a
    #
    @30
    wi
    @46
    vx
    @32
    cvv
    @22
    @32
    wceq
    #
    @47
    @45
    @30
    @38
    @48
    @23
    @36
    @24
    @37
    wph
    @22
    @32
    com
    cdom
    breq1
    @22
    @32
    @10
    sseq1
    3anbi23d
    @48
    @26
    @34
    @29
    @35
    cle
    @48
    @25
    @33
    cM
    @22
    @32
    unieq
    fveq2d
    @22
    @32
    @28
    vy
    esumeq1
    breq12d
    imbi12d
    carsgsiga.2
    vtoclg
    ax-mp
    3adant1r
    mpd3an23
    @14
    @33
    @2
    cM
    @14
    @33
    @3
    @5
    cun
    #
    @2
    @14
    @41
    @42
    @33
    @49
    wceq
    @43
    @44
    @3
    @5
    @10
    @10
    uniprg
    syl2anc
    @2
    @0
    inundif
    syl6eq
    fveq2d
    @14
    @3
    @5
    @28
    @4
    vy
    @6
    @10
    @10
    @14
    @27
    @3
    wceq
    #
    wa
    @27
    @3
    cM
    @14
    @50
    simpr
    fveq2d
    @14
    @27
    @5
    wceq
    #
    wa
    @27
    @5
    cM
    @14
    @51
    simpr
    fveq2d
    @43
    @44
    @14
    @10
    @18
    @3
    cM
    @19
    @43
    ffvelrnd
    #
    @14
    @10
    @18
    @5
    cM
    @19
    @44
    ffvelrnd
    #
    @14
    @3
    @5
    wceq
    #
    @4
    cc0
    wceq
    #
    @4
    cpnf
    wceq
    #
    wo
    @14
    @54
    wa
    #
    @55
    @56
    @57
    @4
    @20
    cc0
    @57
    @3
    c0
    cM
    @54
    @3
    c0
    wceq
    @14
    @54
    @3
    @3
    cin
    @3
    @5
    cin
    @3
    c0
    @3
    @5
    @3
    ineq2
    @3
    inidm
    @2
    @0
    inindif
    3eqtr3g
    adantl
    fveq2d
    wph
    @21
    @13
    @54
    carsgsiga.1
    ad2antrr
    eqtrd
    orcd
    ex
    esumpr2
    3brtr3d
    jca
    @14
    @7
    cxr
    wcel
    @8
    cxr
    wcel
    @9
    @17
    wb
    @14
    @4
    @6
    @14
    @18
    cxr
    @4
    cc0
    cpnf
    iccssxr
    #
    @52
    sseldi
    @14
    @18
    cxr
    @6
    @58
    @53
    sseldi
    xaddcld
    @14
    @18
    cxr
    @8
    @58
    wph
    @10
    @18
    @2
    cM
    carsgval.2
    ffvelrnda
    sseldi
    @7
    @8
    xrletri3
    syl2anc
    mpbird
    ralrimiva
    wph
    @0
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbir2and
end
