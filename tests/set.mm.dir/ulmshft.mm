include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "ulmshftlem.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "eqid.mm"
include "zaddcld.mm"
include "znegcld.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "cz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "syl6eleqr.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "subnegd.mm"
include "fveq2d.mm"
include "wceq.mm"
include "fveq1d.mm"
include "eluzadd.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "pncand.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "cc0.mm"
include "addassd.mm"
include "negidd.mm"
include "oveq2d.mm"
include "addid1d.mm"
include "syl6eqr.mm"
include "mpteq1d.mm"
include "feqmptd.mm"
include "3eqtr4rd.mm"
include "impbid.mm"

theorem ulmshft
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
  assert |- ( ph -> ( F ( ~~>u ` S ) G <-> H ( ~~>u ` S ) G ) )

  proof
    wph
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    cH
    cG
    @0
    wbr
    wph
    cS
    vn
    cF
    cG
    cH
    cK
    cM
    cW
    cZ
    ulmshft.z
    ulmshft.w
    ulmshft.m
    ulmshft.k
    ulmshft.f
    ulmshft.h
    ulmshftlem
    wph
    cS
    vm
    cH
    cG
    cF
    cK
    cneg
    #
    cM
    cK
    caddc
    co
    #
    @2
    @1
    caddc
    co
    #
    cuz
    cfv
    #
    cW
    ulmshft.w
    @4
    eqid
    wph
    cM
    cK
    ulmshft.m
    ulmshft.k
    zaddcld
    wph
    cK
    ulmshft.k
    znegcld
    #
    wph
    cW
    cc
    cS
    cmap
    co
    #
    cH
    wf
    cW
    @6
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
    @9
    @6
    @10
    wph
    @7
    cW
    wcel
    #
    wa
    #
    cZ
    @6
    @8
    cF
    wph
    cZ
    @6
    cF
    wf
    @11
    ulmshft.f
    adantr
    @12
    @8
    cM
    cuz
    cfv
    #
    cZ
    @12
    cM
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @7
    @2
    cuz
    cfv
    #
    wcel
    @8
    @13
    wcel
    wph
    @14
    @11
    ulmshft.m
    adantr
    wph
    @15
    @11
    ulmshft.k
    adantr
    @12
    @7
    cW
    @16
    wph
    @11
    simpr
    ulmshft.w
    syl6eleq
    cK
    cM
    @7
    eluzsub
    syl3anc
    ulmshft.z
    syl6eleqr
    ffvelrnd
    @10
    eqid
    #
    fmptd
    wph
    cW
    @6
    cH
    @10
    ulmshft.h
    feq1d
    mpbird
    wph
    vm
    cZ
    vm
    cv
    #
    @1
    cmin
    co
    #
    cH
    cfv
    #
    cmpt
    vm
    cZ
    @18
    cF
    cfv
    #
    cmpt
    vm
    @4
    @20
    cmpt
    cF
    wph
    vm
    cZ
    @20
    @21
    wph
    @18
    cZ
    wcel
    #
    wa
    #
    @20
    @18
    cK
    caddc
    co
    #
    cH
    cfv
    @24
    @10
    cfv
    #
    @21
    @23
    @19
    @24
    cH
    @23
    @18
    cK
    @23
    @18
    @23
    @18
    @13
    wcel
    #
    @18
    cz
    wcel
    @23
    @18
    cZ
    @13
    wph
    @22
    simpr
    ulmshft.z
    syl6eleq
    #
    cM
    @18
    eluzelz
    syl
    zcnd
    #
    wph
    cK
    cc
    wcel
    @22
    wph
    cK
    ulmshft.k
    zcnd
    #
    adantr
    #
    subnegd
    fveq2d
    @23
    @24
    cH
    @10
    wph
    cH
    @10
    wceq
    @22
    ulmshft.h
    adantr
    fveq1d
    @23
    @25
    @24
    cK
    cmin
    co
    #
    cF
    cfv
    #
    @21
    @23
    @24
    cW
    wcel
    @25
    @32
    wceq
    @23
    @24
    @16
    cW
    @23
    @26
    @15
    @24
    @16
    wcel
    @27
    wph
    @15
    @22
    ulmshft.k
    adantr
    cK
    cM
    @18
    eluzadd
    syl2anc
    ulmshft.w
    syl6eleqr
    vn
    @24
    @9
    @32
    cW
    @10
    @7
    @24
    wceq
    @8
    @31
    cF
    @7
    @24
    cK
    cmin
    oveq1
    fveq2d
    @17
    @31
    cF
    fvex
    fvmpt
    syl
    @23
    @31
    @18
    cF
    @23
    @18
    cK
    @28
    @30
    pncand
    fveq2d
    eqtrd
    3eqtrd
    mpteq2dva
    wph
    vm
    @4
    cZ
    @20
    wph
    @4
    @13
    cZ
    wph
    @3
    cM
    cuz
    wph
    @3
    cM
    cK
    @1
    caddc
    co
    #
    caddc
    co
    cM
    cc0
    caddc
    co
    cM
    wph
    cM
    cK
    @1
    wph
    cM
    ulmshft.m
    zcnd
    #
    @29
    wph
    @1
    @5
    zcnd
    addassd
    wph
    @33
    cc0
    cM
    caddc
    wph
    cK
    @29
    negidd
    oveq2d
    wph
    cM
    @34
    addid1d
    3eqtrd
    fveq2d
    ulmshft.z
    syl6eqr
    mpteq1d
    wph
    vm
    cZ
    @6
    cF
    ulmshft.f
    feqmptd
    3eqtr4rd
    ulmshftlem
    impbid
end
