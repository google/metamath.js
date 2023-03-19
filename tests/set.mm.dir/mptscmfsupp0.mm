include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wfun.mm"
include "csupp.mm"
include "cfn.mm"
include "wss.mm"
include "cfsupp.mm"
include "wbr.mm"
include "mptexg.mm"
include "syl.mm"
include "funmpt.mm"
include "a1i.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fsuppimpd.mm"
include "cv.mm"
include "wne.mm"
include "crab.mm"
include "wa.mm"
include "wceq.mm"
include "csb.mm"
include "simpr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fvmpts.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "csca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "clmod.mm"
include "lmod0vs.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "wb.mm"
include "csbov12g.mm"
include "adantl.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "mpbird.mm"
include "ex.mm"
include "sylbid.mm"
include "necon3d.mm"
include "ss2rabdv.mm"
include "wfn.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "3sstr4d.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"

theorem mptscmfsupp0
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vk: setvar k
  let c.as: class .*
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vd: setvar d
  assume mptscmfsupp0.d: |- ( ph -> D e. V )
  assume mptscmfsupp0.q: |- ( ph -> Q e. LMod )
  assume mptscmfsupp0.r: |- ( ph -> R = ( Scalar ` Q ) )
  assume mptscmfsupp0.k: |- K = ( Base ` Q )
  assume mptscmfsupp0.s: |- ( ( ph /\ k e. D ) -> S e. B )
  assume mptscmfsupp0.w: |- ( ( ph /\ k e. D ) -> W e. K )
  assume mptscmfsupp0.0: |- .0. = ( 0g ` Q )
  assume mptscmfsupp0.z: |- Z = ( 0g ` R )
  assume mptscmfsupp0.m: |- .* = ( .s ` Q )
  assume mptscmfsupp0.f: |- ( ph -> ( k e. D |-> S ) finSupp Z )

  disjoint B k
  disjoint D k
  disjoint K k
  disjoint k ph
  disjoint .* k
  disjoint D d
  disjoint d k
  disjoint S d
  disjoint V d
  disjoint W d
  disjoint Z d
  disjoint d ph
  disjoint .* d
  disjoint .0. d
  assert |- ( ph -> ( k e. D |-> ( S .* W ) ) finSupp .0. )

  proof
    wph
    vk
    cD
    cS
    cW
    c.as
    co
    #
    cmpt
    #
    cvv
    wcel
    #
    @1
    wfun
    #
    c.0
    cvv
    wcel
    #
    vk
    cD
    cS
    cmpt
    #
    cZ
    csupp
    co
    #
    cfn
    wcel
    @1
    c.0
    csupp
    co
    #
    @6
    wss
    @1
    c.0
    cfsupp
    wbr
    wph
    cD
    cV
    wcel
    #
    @2
    mptscmfsupp0.d
    vk
    cD
    @0
    cV
    mptexg
    syl
    @3
    wph
    vk
    cD
    @0
    funmpt
    a1i
    @4
    wph
    c.0
    cQ
    c0g
    cfv
    cvv
    mptscmfsupp0.0
    cQ
    c0g
    fvex
    eqeltri
    a1i
    #
    wph
    @5
    cZ
    mptscmfsupp0.f
    fsuppimpd
    wph
    vd
    cv
    #
    @1
    cfv
    #
    c.0
    wne
    #
    vd
    cD
    crab
    #
    @10
    @5
    cfv
    #
    cZ
    wne
    #
    vd
    cD
    crab
    #
    @7
    @6
    wph
    @12
    @15
    vd
    cD
    wph
    @10
    cD
    wcel
    #
    wa
    #
    @14
    cZ
    @11
    c.0
    @18
    @14
    cZ
    wceq
    vk
    @10
    cS
    csb
    #
    cZ
    wceq
    #
    @11
    c.0
    wceq
    #
    @18
    @14
    @19
    cZ
    @18
    @17
    @19
    cB
    wcel
    #
    @14
    @19
    wceq
    wph
    @17
    simpr
    #
    @18
    @17
    cS
    cB
    wcel
    #
    vk
    cD
    wral
    #
    @22
    @23
    wph
    @25
    @17
    wph
    @24
    vk
    cD
    mptscmfsupp0.s
    ralrimiva
    #
    adantr
    vk
    @10
    cD
    cS
    cB
    rspcsbela
    syl2anc
    vk
    @10
    cS
    cD
    @5
    cB
    @5
    eqid
    #
    fvmpts
    syl2anc
    eqeq1d
    @18
    @20
    @21
    @18
    @20
    wa
    @21
    @19
    vk
    @10
    cW
    csb
    #
    c.as
    co
    #
    c.0
    wceq
    #
    @20
    @18
    @29
    cZ
    @28
    c.as
    co
    #
    c.0
    @19
    cZ
    @28
    c.as
    oveq1
    @18
    @31
    cQ
    csca
    cfv
    #
    c0g
    cfv
    #
    @28
    c.as
    co
    #
    c.0
    @18
    cZ
    @33
    @28
    c.as
    @18
    cZ
    cR
    c0g
    cfv
    #
    @33
    mptscmfsupp0.z
    @18
    cR
    @32
    c0g
    wph
    cR
    @32
    wceq
    @17
    mptscmfsupp0.r
    adantr
    fveq2d
    syl5eq
    oveq1d
    @18
    cQ
    clmod
    wcel
    #
    @28
    cK
    wcel
    #
    @34
    c.0
    wceq
    wph
    @36
    @17
    mptscmfsupp0.q
    adantr
    @18
    @17
    cW
    cK
    wcel
    #
    vk
    cD
    wral
    #
    @37
    @23
    wph
    @39
    @17
    wph
    @38
    vk
    cD
    mptscmfsupp0.w
    ralrimiva
    adantr
    vk
    @10
    cD
    cW
    cK
    rspcsbela
    syl2anc
    c.as
    @32
    @33
    cK
    cQ
    @28
    c.0
    mptscmfsupp0.k
    @32
    eqid
    mptscmfsupp0.m
    @33
    eqid
    mptscmfsupp0.0
    lmod0vs
    syl2anc
    eqtrd
    sylan9eqr
    @18
    @21
    @30
    wb
    @20
    @18
    @11
    @29
    c.0
    @18
    @11
    vk
    @10
    @0
    csb
    #
    @29
    @18
    @17
    @40
    cvv
    wcel
    @11
    @40
    wceq
    @23
    @18
    @40
    @29
    cvv
    @17
    @40
    @29
    wceq
    wph
    vk
    @10
    cS
    cW
    c.as
    cD
    csbov12g
    adantl
    #
    @19
    @28
    c.as
    ovex
    syl6eqel
    vk
    @10
    @0
    cD
    @1
    cvv
    @1
    eqid
    #
    fvmpts
    syl2anc
    @41
    eqtrd
    eqeq1d
    adantr
    mpbird
    ex
    sylbid
    necon3d
    ss2rabdv
    wph
    @1
    cD
    wfn
    #
    @8
    @4
    @7
    @13
    wceq
    @0
    cvv
    wcel
    #
    vk
    cD
    wral
    @43
    wph
    @44
    vk
    cD
    cS
    cW
    c.as
    ovex
    rgenw
    vk
    cD
    @0
    @1
    cvv
    @42
    fnmpt
    mp1i
    mptscmfsupp0.d
    @9
    vd
    @1
    cV
    cvv
    cD
    c.0
    suppvalfn
    syl3anc
    wph
    @5
    cD
    wfn
    #
    @8
    cZ
    cvv
    wcel
    #
    @6
    @16
    wceq
    wph
    @25
    @45
    @26
    vk
    cD
    cS
    @5
    cB
    @27
    fnmpt
    syl
    mptscmfsupp0.d
    @46
    wph
    cZ
    @35
    cvv
    mptscmfsupp0.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    vd
    @5
    cV
    cvv
    cD
    cZ
    suppvalfn
    syl3anc
    3sstr4d
    @6
    @1
    cvv
    cvv
    c.0
    suppssfifsupp
    syl32anc
end
