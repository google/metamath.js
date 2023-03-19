include "cc0.mm"
include "cfwddifn.mm"
include "co.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "cbc.mm"
include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "csu.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "a1i.mm"
include "cc.mm"
include "sseldd.mm"
include "wceq.mm"
include "csn.mm"
include "cz.mm"
include "0z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "velsn.mm"
include "bitri.mm"
include "wa.mm"
include "oveq2.mm"
include "adantl.mm"
include "addid1d.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "sylan2b.mm"
include "fwddifnval.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "ffvelrnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "bcnn.mm"
include "syl6eq.mm"
include "0m0e0.mm"
include "neg1cn.mm"
include "exp0.mm"
include "oveq12d.mm"
include "fsum1.mm"
include "sylancr.mm"

theorem fwddifn0
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume fwddifn0.1: |- ( ph -> A C_ CC )
  assume fwddifn0.2: |- ( ph -> F : A --> CC )
  assume fwddifn0.3: |- ( ph -> X e. A )


  assert |- ( ph -> ( ( 0 _/_\^n F ) ` X ) = ( F ` X ) )

  proof
    wph
    cX
    cc0
    cF
    cfwddifn
    co
    cfv
    cc0
    cc0
    cfz
    co
    #
    cc0
    vk
    cv
    #
    cbc
    co
    #
    c1
    cneg
    #
    cc0
    @1
    cmin
    co
    #
    cexp
    co
    #
    cX
    @1
    caddc
    co
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cX
    cF
    cfv
    #
    wph
    cA
    vk
    cF
    cc0
    cX
    cc0
    cn0
    wcel
    #
    wph
    0nn0
    a1i
    fwddifn0.1
    fwddifn0.2
    wph
    cA
    cc
    cX
    fwddifn0.1
    fwddifn0.3
    sseldd
    #
    @1
    @0
    wcel
    #
    wph
    @1
    cc0
    wceq
    #
    @6
    cA
    wcel
    @14
    @1
    cc0
    csn
    #
    wcel
    @15
    @0
    @16
    @1
    cc0
    cz
    wcel
    #
    @0
    @16
    wceq
    0z
    cc0
    fzsn
    ax-mp
    eleq2i
    vk
    cc0
    velsn
    bitri
    wph
    @15
    wa
    @6
    cX
    cc0
    caddc
    co
    #
    cA
    @15
    @6
    @18
    wceq
    wph
    @1
    cc0
    cX
    caddc
    oveq2
    #
    adantl
    wph
    @18
    cA
    wcel
    @15
    wph
    @18
    cX
    cA
    wph
    cX
    @13
    addid1d
    #
    fwddifn0.3
    eqeltrd
    adantr
    eqeltrd
    sylan2b
    fwddifnval
    wph
    @10
    c1
    c1
    @18
    cF
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @11
    wph
    @17
    @23
    cc
    wcel
    @10
    @23
    wceq
    0z
    wph
    @23
    @11
    cc
    wph
    @23
    c1
    @11
    cmul
    co
    #
    @11
    wph
    @22
    @11
    c1
    cmul
    wph
    @22
    @24
    @11
    wph
    @21
    @11
    c1
    cmul
    wph
    @18
    cX
    cF
    @20
    fveq2d
    oveq2d
    wph
    @11
    wph
    cA
    cc
    cX
    cF
    fwddifn0.2
    fwddifn0.3
    ffvelrnd
    #
    mulid2d
    #
    eqtrd
    oveq2d
    @26
    eqtrd
    #
    @25
    eqeltrd
    @9
    @23
    vk
    cc0
    @15
    @2
    c1
    @8
    @22
    cmul
    @15
    @2
    cc0
    cc0
    cbc
    co
    #
    c1
    @1
    cc0
    cc0
    cbc
    oveq2
    @12
    @28
    c1
    wceq
    0nn0
    cc0
    bcnn
    ax-mp
    syl6eq
    @15
    @5
    c1
    @7
    @21
    cmul
    @15
    @5
    @3
    cc0
    cexp
    co
    #
    c1
    @15
    @4
    cc0
    @3
    cexp
    @15
    @4
    cc0
    cc0
    cmin
    co
    cc0
    @1
    cc0
    cc0
    cmin
    oveq2
    0m0e0
    syl6eq
    oveq2d
    @3
    cc
    wcel
    @29
    c1
    wceq
    neg1cn
    @3
    exp0
    ax-mp
    syl6eq
    @15
    @6
    @18
    cF
    @19
    fveq2d
    oveq12d
    oveq12d
    fsum1
    sylancr
    @27
    eqtrd
    eqtrd
end
