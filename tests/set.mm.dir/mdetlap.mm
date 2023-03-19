include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cneg.mm"
include "caddc.mm"
include "cexp.mm"
include "csmat.mm"
include "ccrg.mm"
include "wcel.mm"
include "wceq.mm"
include "mdetlap1.mm"
include "syl3anc.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "simpr.mm"
include "madjusmdet.mm"
include "oveq2d.mm"
include "cbs.mm"
include "eqid.mm"
include "matecld.mm"
include "cz.mm"
include "wf.mm"
include "crg.mm"
include "zring.mm"
include "crh.mm"
include "crngring.mm"
include "syl.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "3syl.mm"
include "cn0.mm"
include "1zzd.mm"
include "znegcld.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnaddcld.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "crngcom.mm"
include "oveq1d.mm"
include "cmin.mm"
include "cmat.mm"
include "smatcl.mm"
include "mdetcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"

theorem mdetlap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let vj: setvar j
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vl: setvar l
  let cP: class P
  let cQ: class Q
  assume madjusmdet.b: |- B = ( Base ` A )
  assume madjusmdet.a: |- A = ( ( 1 ... N ) Mat R )
  assume madjusmdet.d: |- D = ( ( 1 ... N ) maDet R )
  assume madjusmdet.k: |- K = ( ( 1 ... N ) maAdju R )
  assume madjusmdet.t: |- .x. = ( .r ` R )
  assume madjusmdet.z: |- Z = ( ZRHom ` R )
  assume madjusmdet.e: |- E = ( ( 1 ... ( N - 1 ) ) maDet R )
  assume madjusmdet.n: |- ( ph -> N e. NN )
  assume madjusmdet.r: |- ( ph -> R e. CRing )
  assume madjusmdet.i: |- ( ph -> I e. ( 1 ... N ) )
  assume madjusmdet.j: |- ( ph -> J e. ( 1 ... N ) )
  assume madjusmdet.m: |- ( ph -> M e. B )

  disjoint B j
  disjoint I j
  disjoint J j
  disjoint M j
  disjoint N j
  disjoint R j
  disjoint j ph
  disjoint .x. j
  disjoint A j
  disjoint K j
  disjoint B i
  disjoint i j
  disjoint I i
  disjoint I k
  disjoint I l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint J i
  disjoint J k
  disjoint J l
  disjoint M i
  disjoint M k
  disjoint M l
  disjoint N i
  disjoint N k
  disjoint N l
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint P l
  disjoint Q i
  disjoint Q j
  disjoint Q k
  disjoint Q l
  disjoint R i
  disjoint R k
  disjoint R l
  disjoint i ph
  assert |- ( ph -> ( D ` M ) = ( R gsum ( j e. ( 1 ... N ) |-> ( ( Z ` ( -u 1 ^ ( I + j ) ) ) .x. ( ( I M j ) .x. ( E ` ( I ( subMat1 ` M ) j ) ) ) ) ) ) )

  proof
    wph
    cM
    cD
    cfv
    #
    cR
    vj
    c1
    cN
    cfz
    co
    #
    cI
    vj
    cv
    #
    cM
    co
    #
    @2
    cI
    cM
    cK
    cfv
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vj
    @1
    c1
    cneg
    #
    cI
    @2
    caddc
    co
    #
    cexp
    co
    #
    cZ
    cfv
    #
    @3
    cI
    @2
    cM
    csmat
    cfv
    co
    #
    cE
    cfv
    #
    c.x
    co
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    cI
    @1
    wcel
    #
    @0
    @7
    wceq
    madjusmdet.r
    madjusmdet.m
    madjusmdet.i
    cA
    cB
    cD
    cR
    c.x
    vj
    cI
    cK
    cM
    @1
    madjusmdet.a
    madjusmdet.b
    madjusmdet.d
    madjusmdet.k
    madjusmdet.t
    mdetlap1
    syl3anc
    wph
    @6
    @15
    cR
    cgsu
    wph
    vj
    @1
    @5
    @14
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @5
    @3
    @11
    @13
    c.x
    co
    #
    c.x
    co
    #
    @14
    @20
    @4
    @21
    @3
    c.x
    @20
    cA
    cB
    cD
    cR
    c.x
    cE
    cI
    @2
    cK
    cM
    cN
    cZ
    madjusmdet.b
    madjusmdet.a
    madjusmdet.d
    madjusmdet.k
    madjusmdet.t
    madjusmdet.z
    madjusmdet.e
    wph
    cN
    cn
    wcel
    @19
    madjusmdet.n
    adantr
    #
    wph
    @16
    @19
    madjusmdet.r
    adantr
    #
    wph
    @18
    @19
    madjusmdet.i
    adantr
    #
    wph
    @19
    simpr
    #
    wph
    @17
    @19
    madjusmdet.m
    adantr
    #
    madjusmdet
    oveq2d
    @20
    @3
    @11
    c.x
    co
    #
    @13
    c.x
    co
    #
    @11
    @3
    c.x
    co
    #
    @13
    c.x
    co
    #
    @22
    @14
    @20
    @28
    @30
    @13
    c.x
    @20
    @16
    @3
    cR
    cbs
    cfv
    #
    wcel
    #
    @11
    @32
    wcel
    #
    @28
    @30
    wceq
    @24
    @20
    cA
    cB
    cR
    cI
    @2
    @32
    cM
    @1
    madjusmdet.a
    @32
    eqid
    #
    madjusmdet.b
    @25
    @26
    @27
    matecld
    #
    @20
    cz
    @32
    @10
    cZ
    wph
    cz
    @32
    cZ
    wf
    #
    @19
    wph
    cR
    crg
    wcel
    #
    cZ
    zring
    cR
    crh
    co
    wcel
    @37
    wph
    @16
    @38
    madjusmdet.r
    cR
    crngring
    #
    syl
    cR
    cZ
    madjusmdet.z
    zrhrhm
    cz
    @32
    zring
    cR
    cZ
    zringbas
    @35
    rhmf
    3syl
    adantr
    @20
    @8
    cz
    wcel
    @9
    cn0
    wcel
    @10
    cz
    wcel
    @20
    c1
    @20
    1zzd
    znegcld
    @20
    @9
    @20
    cI
    @2
    @20
    @1
    cn
    cI
    cN
    fz1ssnn
    #
    @25
    sseldi
    @20
    @1
    cn
    @2
    @40
    @26
    sseldi
    nnaddcld
    nnnn0d
    @8
    @9
    zexpcl
    syl2anc
    ffvelrnd
    #
    @32
    cR
    c.x
    @3
    @11
    @35
    madjusmdet.t
    crngcom
    syl3anc
    oveq1d
    @20
    @38
    @33
    @34
    @13
    @32
    wcel
    #
    @29
    @22
    wceq
    @20
    @16
    @38
    @24
    @39
    syl
    #
    @36
    @41
    @20
    @16
    @12
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @42
    @24
    @20
    cA
    cB
    @46
    cR
    @12
    cI
    @2
    cM
    cN
    madjusmdet.a
    madjusmdet.b
    @46
    eqid
    #
    @12
    eqid
    @23
    @25
    @26
    @27
    smatcl
    @45
    @46
    cE
    cR
    @32
    @12
    @44
    madjusmdet.e
    @45
    eqid
    @47
    @35
    mdetcl
    syl2anc
    #
    @32
    cR
    c.x
    @3
    @11
    @13
    @35
    madjusmdet.t
    ringass
    syl13anc
    @20
    @38
    @34
    @33
    @42
    @31
    @14
    wceq
    @43
    @41
    @36
    @48
    @32
    cR
    c.x
    @11
    @3
    @13
    @35
    madjusmdet.t
    ringass
    syl13anc
    3eqtr3d
    eqtrd
    mpteq2dva
    oveq2d
    eqtrd
end
