include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "ad2antrr.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "eqidd.mm"
include "simplr.mm"
include "simpr.mm"
include "ulmi.mm"
include "caddc.mm"
include "syl6eleq.mm"
include "ad3antrrr.mm"
include "eluzadd.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "wi.mm"
include "eluzelz.mm"
include "syl.mm"
include "adantr.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "ralrimdva.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "zaddcld.mm"
include "cmpt.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "oveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "eqtrd.mm"
include "ulmcl.mm"
include "adantl.mm"
include "ulmscl.mm"
include "ulm2.mm"
include "ex.mm"

theorem ulmshftlem
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vz: setvar z
  assume ulmshft.z: |- Z = ( ZZ>= ` M )
  assume ulmshft.w: |- W = ( ZZ>= ` ( M + K ) )
  assume ulmshft.m: |- ( ph -> M e. ZZ )
  assume ulmshft.k: |- ( ph -> K e. ZZ )
  assume ulmshft.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulmshft.h: |- ( ph -> H = ( n e. W |-> ( F ` ( n - K ) ) ) )

  disjoint n ph
  disjoint W n
  disjoint F n
  disjoint K n
  disjoint S n
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i x
  disjoint i z
  disjoint G i
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j z
  disjoint G j
  disjoint k m
  disjoint k x
  disjoint k z
  disjoint G k
  disjoint m x
  disjoint m z
  disjoint G m
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint i n
  disjoint i ph
  disjoint j n
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint m n
  disjoint m ph
  disjoint n x
  disjoint n z
  disjoint ph x
  disjoint ph z
  disjoint W i
  disjoint W j
  disjoint W x
  disjoint Z i
  disjoint Z k
  disjoint Z m
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F x
  disjoint F z
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K x
  disjoint K z
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S x
  disjoint S z
  disjoint H j
  disjoint H k
  disjoint H m
  disjoint H x
  disjoint H z
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M x
  disjoint M z
  assert |- ( ph -> ( F ( ~~>u ` S ) G -> H ( ~~>u ` S ) G ) )

  proof
    wph
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    #
    cH
    cG
    @0
    wbr
    #
    wph
    @1
    wa
    #
    @2
    vz
    cv
    #
    vk
    cv
    #
    cK
    cmin
    co
    #
    cF
    cfv
    #
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cW
    wrex
    #
    vx
    crp
    wral
    @3
    @18
    vx
    crp
    @3
    @12
    crp
    wcel
    #
    wa
    #
    @4
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @9
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    vi
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vi
    cZ
    wrex
    @18
    @20
    vz
    @9
    @23
    @12
    cS
    vi
    vm
    cF
    cG
    cM
    cZ
    ulmshft.z
    wph
    cM
    cz
    wcel
    #
    @1
    @19
    ulmshft.m
    ad2antrr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    @1
    @19
    ulmshft.f
    ad2antrr
    @20
    @21
    cZ
    wcel
    @4
    cS
    wcel
    #
    wa
    wa
    @23
    eqidd
    @20
    @34
    wa
    @9
    eqidd
    wph
    @1
    @19
    simplr
    @3
    @19
    simpr
    ulmi
    @20
    @30
    @18
    vi
    cZ
    @20
    @28
    cZ
    wcel
    #
    wa
    #
    @28
    cK
    caddc
    co
    #
    cW
    wcel
    @30
    @14
    vk
    @37
    cuz
    cfv
    #
    wral
    #
    @18
    @36
    @37
    cM
    cK
    caddc
    co
    #
    cuz
    cfv
    #
    cW
    @36
    @28
    cM
    cuz
    cfv
    #
    wcel
    #
    cK
    cz
    wcel
    #
    @37
    @41
    wcel
    @36
    @28
    cZ
    @42
    @20
    @35
    simpr
    ulmshft.z
    syl6eleq
    #
    wph
    @44
    @1
    @19
    @35
    ulmshft.k
    ad3antrrr
    cK
    cM
    @28
    eluzadd
    syl2anc
    ulmshft.w
    syl6eleqr
    @36
    @30
    @14
    vk
    @38
    @36
    @5
    @38
    wcel
    #
    wa
    #
    @6
    @29
    wcel
    #
    @30
    @14
    wi
    @47
    @28
    cz
    wcel
    #
    @44
    @46
    @48
    @36
    @49
    @46
    @36
    @43
    @49
    @45
    cM
    @28
    eluzelz
    syl
    adantr
    @3
    @44
    @19
    @35
    @46
    wph
    @44
    @1
    ulmshft.k
    adantr
    ad3antrrr
    @36
    @46
    simpr
    cK
    @28
    @5
    eluzsub
    syl3anc
    @27
    @14
    vm
    @6
    @29
    @21
    @6
    wceq
    #
    @26
    @13
    vz
    cS
    @50
    @25
    @11
    @12
    clt
    @50
    @24
    @10
    cabs
    @50
    @23
    @8
    @9
    cmin
    @50
    @4
    @22
    @7
    @21
    @6
    cF
    fveq2
    fveq1d
    oveq1d
    fveq2d
    breq1d
    ralbidv
    rspcv
    syl
    ralrimdva
    @17
    @39
    vj
    @37
    cW
    @15
    @37
    wceq
    @14
    vk
    @16
    @38
    @15
    @37
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    mpd
    ralrimiva
    @3
    vx
    vz
    @9
    @8
    cS
    vj
    vk
    cH
    cG
    @40
    cvv
    cW
    ulmshft.w
    wph
    @40
    cz
    wcel
    @1
    wph
    cM
    cK
    ulmshft.m
    ulmshft.k
    zaddcld
    adantr
    wph
    cW
    @32
    cH
    wf
    #
    @1
    wph
    @51
    cW
    @32
    vn
    cW
    vn
    cv
    #
    cK
    cmin
    co
    #
    cF
    cfv
    #
    cmpt
    #
    wf
    wph
    vn
    cW
    @54
    @32
    @55
    wph
    @52
    cW
    wcel
    #
    wa
    #
    cZ
    @32
    @53
    cF
    wph
    @33
    @56
    ulmshft.f
    adantr
    @57
    @53
    @42
    cZ
    @57
    @31
    @44
    @52
    @41
    wcel
    @53
    @42
    wcel
    wph
    @31
    @56
    ulmshft.m
    adantr
    wph
    @44
    @56
    ulmshft.k
    adantr
    @57
    @52
    cW
    @41
    wph
    @56
    simpr
    ulmshft.w
    syl6eleq
    cK
    cM
    @52
    eluzsub
    syl3anc
    ulmshft.z
    syl6eleqr
    ffvelrnd
    @55
    eqid
    #
    fmptd
    wph
    cW
    @32
    cH
    @55
    ulmshft.h
    feq1d
    mpbird
    adantr
    @3
    @5
    cW
    wcel
    #
    @34
    wa
    #
    wa
    #
    @4
    @5
    cH
    cfv
    #
    @7
    @61
    @62
    @5
    @55
    cfv
    #
    @7
    @61
    @5
    cH
    @55
    wph
    cH
    @55
    wceq
    @1
    @60
    ulmshft.h
    ad2antrr
    fveq1d
    @59
    @63
    @7
    wceq
    @3
    @34
    vn
    @5
    @54
    @7
    cW
    @55
    @52
    @5
    wceq
    @53
    @6
    cF
    @52
    @5
    cK
    cmin
    oveq1
    fveq2d
    @58
    @6
    cF
    fvex
    fvmpt
    ad2antrl
    eqtrd
    fveq1d
    @3
    @34
    wa
    @9
    eqidd
    @1
    cS
    cc
    cG
    wf
    wph
    cS
    cF
    cG
    ulmcl
    adantl
    @1
    cS
    cvv
    wcel
    wph
    cS
    cF
    cG
    ulmscl
    adantl
    ulm2
    mpbird
    ex
end
