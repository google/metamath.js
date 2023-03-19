include "cn.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "crp.mm"
include "w3a.mm"
include "cv.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "nnne0d.mm"
include "wceq.mm"
include "c0p.mm"
include "cply.mm"
include "wb.mm"
include "dgreq0.mm"
include "syl.mm"
include "cdgr.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "syl6bir.mm"
include "necon3d.mm"
include "mpd.mm"
include "neeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sylib.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "ccxp.mm"
include "wf.mm"
include "plyf.mm"
include "0cn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "cn0.mm"
include "coef3.mm"
include "simpld.mm"
include "nnnn0d.mm"
include "ffvelrnd.mm"
include "simprd.mm"
include "divcld.mm"
include "negcld.mm"
include "nnrecred.mm"
include "recnd.mm"
include "cxpcld.mm"
include "cabs.mm"
include "caddc.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "absrpcld.mm"
include "fzfid.mm"
include "peano2nn0.mm"
include "elfzuz.mm"
include "eluznn0.mm"
include "syl2an.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "absge0d.mm"
include "fsumge0.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "1rp.mm"
include "ifcl.mm"
include "3jca.mm"
include "jca.mm"

theorem ftalem4
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let cD: class D
  let cE: class E
  let vw: setvar w
  let vy: setvar y
  let cJ: class J
  let cR: class R
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem4.5: |- ( ph -> ( F ` 0 ) =/= 0 )
  assume ftalem4.6: |- K = inf ( { n e. NN | ( A ` n ) =/= 0 } , RR , < )
  assume ftalem4.7: |- T = ( -u ( ( F ` 0 ) / ( A ` K ) ) ^c ( 1 / K ) )
  assume ftalem4.8: |- U = ( ( abs ` ( F ` 0 ) ) / ( sum_ k e. ( ( K + 1 ) ... N ) ( abs ` ( ( A ` k ) x. ( T ^ k ) ) ) + 1 ) )
  assume ftalem4.9: |- X = if ( 1 <_ U , 1 , U )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint F k
  disjoint F n
  disjoint k ph
  disjoint S k
  disjoint T k
  disjoint X k
  disjoint X n
  disjoint k r
  disjoint k s
  disjoint k x
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint A x
  disjoint s z
  disjoint D s
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint E r
  disjoint N r
  disjoint N s
  disjoint N x
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s w
  disjoint s y
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J s
  disjoint J x
  disjoint J z
  disjoint ph s
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S s
  disjoint T r
  disjoint T x
  disjoint U r
  disjoint U x
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( ( K e. NN /\ ( A ` K ) =/= 0 ) /\ ( T e. CC /\ U e. RR+ /\ X e. RR+ ) ) )

  proof
    wph
    cK
    cn
    wcel
    #
    cK
    cA
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cT
    cc
    wcel
    #
    cU
    crp
    wcel
    #
    cX
    crp
    wcel
    #
    w3a
    wph
    cK
    vn
    cv
    #
    cA
    cfv
    #
    cc0
    wne
    #
    vn
    cn
    crab
    #
    wcel
    @3
    wph
    cK
    @10
    cr
    clt
    cinf
    #
    @10
    ftalem4.6
    wph
    @10
    c1
    cuz
    cfv
    #
    wss
    @10
    c0
    wne
    #
    @11
    @10
    wcel
    @10
    cn
    @12
    @9
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    wph
    cN
    @10
    wcel
    #
    @13
    wph
    cN
    cn
    wcel
    cN
    cA
    cfv
    #
    cc0
    wne
    #
    @14
    ftalem.4
    wph
    cN
    cc0
    wne
    @16
    wph
    cN
    ftalem.4
    nnne0d
    wph
    @15
    cc0
    cN
    cc0
    wph
    @15
    cc0
    wceq
    #
    cF
    c0p
    wceq
    #
    cN
    cc0
    wceq
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    @18
    @17
    wb
    ftalem.3
    cA
    cS
    cF
    cN
    ftalem.2
    ftalem.1
    dgreq0
    syl
    @18
    cN
    cF
    cdgr
    cfv
    #
    cc0
    ftalem.2
    @18
    @20
    c0p
    cdgr
    cfv
    cc0
    cF
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    syl5eq
    syl6bir
    necon3d
    mpd
    @9
    @16
    vn
    cN
    cn
    @7
    cN
    wceq
    @8
    @15
    cc0
    @7
    cN
    cA
    fveq2
    neeq1d
    elrab
    sylanbrc
    @10
    cN
    ne0i
    syl
    @10
    c1
    infssuzcl
    sylancr
    syl5eqel
    @9
    @2
    vn
    cK
    cn
    @7
    cK
    wceq
    @8
    @1
    cc0
    @7
    cK
    cA
    fveq2
    neeq1d
    elrab
    sylib
    #
    wph
    @4
    @5
    @6
    wph
    cT
    cc0
    cF
    cfv
    #
    @1
    cdiv
    co
    #
    cneg
    #
    c1
    cK
    cdiv
    co
    #
    ccxp
    co
    cc
    ftalem4.7
    wph
    @24
    @25
    wph
    @23
    wph
    @22
    @1
    wph
    cc
    cc
    cF
    wf
    #
    cc0
    cc
    wcel
    @22
    cc
    wcel
    wph
    @19
    @26
    ftalem.3
    cS
    cF
    plyf
    syl
    0cn
    cc
    cc
    cc0
    cF
    ffvelrn
    sylancl
    #
    wph
    cn0
    cc
    cK
    cA
    wph
    @19
    cn0
    cc
    cA
    wf
    ftalem.3
    cA
    cS
    cF
    ftalem.1
    coef3
    syl
    #
    wph
    cK
    wph
    @0
    @2
    @21
    simpld
    #
    nnnn0d
    #
    ffvelrnd
    wph
    @0
    @2
    @21
    simprd
    divcld
    negcld
    wph
    @25
    wph
    cK
    @29
    nnrecred
    recnd
    cxpcld
    syl5eqel
    #
    wph
    cU
    @22
    cabs
    cfv
    #
    cK
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    cT
    @35
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    vk
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    crp
    ftalem4.8
    wph
    @32
    @41
    wph
    @22
    @27
    ftalem4.5
    absrpcld
    wph
    @40
    wph
    @34
    @39
    vk
    wph
    @33
    cN
    fzfid
    #
    wph
    @35
    @34
    wcel
    #
    wa
    #
    @38
    @44
    @36
    @37
    wph
    @43
    @35
    cn0
    wcel
    #
    @36
    cc
    wcel
    wph
    @33
    cn0
    wcel
    #
    @35
    @33
    cuz
    cfv
    wcel
    @45
    @43
    wph
    cK
    cn0
    wcel
    @46
    @30
    cK
    peano2nn0
    syl
    @35
    @33
    cN
    elfzuz
    @35
    @33
    eluznn0
    syl2an
    #
    wph
    cn0
    cc
    @35
    cA
    @28
    ffvelrnda
    syldan
    wph
    @43
    @45
    @37
    cc
    wcel
    #
    @47
    wph
    @4
    @45
    @48
    @31
    cT
    @35
    expcl
    sylan
    syldan
    mulcld
    #
    abscld
    #
    fsumrecl
    wph
    @34
    @39
    vk
    @42
    @50
    @44
    @38
    @49
    absge0d
    fsumge0
    ge0p1rpd
    rpdivcld
    syl5eqel
    #
    wph
    cX
    c1
    cU
    cle
    wbr
    #
    c1
    cU
    cif
    #
    crp
    ftalem4.9
    wph
    c1
    crp
    wcel
    @5
    @53
    crp
    wcel
    1rp
    @51
    @52
    c1
    cU
    crp
    ifcl
    sylancr
    syl5eqel
    3jca
    jca
end
