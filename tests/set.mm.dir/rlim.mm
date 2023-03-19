include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cvv.mm"
include "rlimrel.mm"
include "brrelex2i.mm"
include "a1i.mm"
include "elex.mm"
include "ad2antrl.mm"
include "wb.mm"
include "wf.mm"
include "wss.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "wceq.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "simpl.mm"
include "dmeqd.mm"
include "fveq1.mm"
include "oveq12.mm"
include "sylan.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "df-rlim.mm"
include "brabga.mm"
include "anass.mm"
include "syl6bb.mm"
include "ex.mm"
include "syl.mm"
include "pm5.21ndd.mm"
include "biantrurd.mm"
include "fdm.mm"
include "raleqdv.mm"
include "oveq1d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "3bitr2d.mm"

theorem rlim
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  assume rlim.1: |- ( ph -> F : A --> CC )
  assume rlim.2: |- ( ph -> A C_ RR )
  assume rlim.4: |- ( ( ph /\ z e. A ) -> ( F ` z ) = B )

  disjoint A z
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint C f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint F f
  disjoint F w
  assert |- ( ph -> ( F ~~>r C <-> ( C e. CC /\ A. x e. RR+ E. y e. RR A. z e. A ( y <_ z -> ( abs ` ( B - C ) ) < x ) ) ) )

  proof
    wph
    cF
    cC
    crli
    wbr
    #
    cF
    cc
    cr
    cpm
    co
    #
    wcel
    #
    cC
    cc
    wcel
    #
    vy
    cv
    vz
    cv
    #
    cle
    wbr
    #
    @4
    cF
    cfv
    #
    cC
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
    wi
    #
    vz
    cF
    cdm
    #
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    wa
    #
    @16
    @3
    @5
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    cC
    cvv
    wcel
    #
    @0
    @17
    @0
    @25
    wi
    wph
    cF
    cC
    crli
    rlimrel
    brrelex2i
    a1i
    @17
    @25
    wi
    wph
    @3
    @25
    @2
    @15
    cC
    cc
    elex
    ad2antrl
    a1i
    wph
    @2
    @25
    @0
    @17
    wb
    #
    wi
    wph
    cA
    cc
    cF
    wf
    #
    cA
    cr
    wss
    #
    @2
    rlim.1
    rlim.2
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @27
    @28
    wa
    @2
    cnex
    reex
    cc
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    #
    @2
    @25
    @26
    @2
    @25
    wa
    @0
    @2
    @3
    wa
    #
    @15
    wa
    #
    @17
    vf
    cv
    #
    @1
    wcel
    #
    vw
    cv
    #
    cc
    wcel
    #
    wa
    #
    @5
    @4
    @32
    cfv
    #
    @34
    cmin
    co
    #
    cabs
    cfv
    #
    @9
    clt
    wbr
    #
    wi
    #
    vz
    @32
    cdm
    #
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @31
    vf
    vw
    cF
    cC
    crli
    @1
    cvv
    @32
    cF
    wceq
    #
    @34
    cC
    wceq
    #
    wa
    #
    @36
    @30
    @45
    @15
    @46
    @33
    @2
    @47
    @35
    @3
    @32
    cF
    @1
    eleq1
    @34
    cC
    cc
    eleq1
    bi2anan9
    @48
    @44
    @14
    vx
    crp
    @48
    @43
    @13
    vy
    cr
    @48
    @41
    @11
    vz
    @42
    @12
    @48
    @32
    cF
    @46
    @47
    simpl
    dmeqd
    @48
    @40
    @10
    @5
    @48
    @39
    @8
    @9
    clt
    @48
    @38
    @7
    cabs
    @46
    @37
    @6
    wceq
    @47
    @38
    @7
    wceq
    @4
    @32
    cF
    fveq1
    @37
    @6
    @34
    cC
    cmin
    oveq12
    sylan
    fveq2d
    breq1d
    imbi2d
    raleqbidv
    rexbidv
    ralbidv
    anbi12d
    vw
    vx
    vy
    vz
    vf
    df-rlim
    brabga
    @2
    @3
    @15
    anass
    syl6bb
    ex
    syl
    pm5.21ndd
    wph
    @2
    @16
    @29
    biantrurd
    wph
    @15
    @24
    @3
    wph
    @14
    @23
    vx
    crp
    wph
    @13
    @22
    vy
    cr
    wph
    @13
    @11
    vz
    cA
    wral
    @22
    wph
    @11
    vz
    @12
    cA
    wph
    @27
    @12
    cA
    wceq
    rlim.1
    cA
    cc
    cF
    fdm
    syl
    raleqdv
    wph
    @11
    @21
    vz
    cA
    wph
    @4
    cA
    wcel
    wa
    #
    @10
    @20
    @5
    @49
    @8
    @19
    @9
    clt
    @49
    @7
    @18
    cabs
    @49
    @6
    cB
    cC
    cmin
    rlim.4
    oveq1d
    fveq2d
    breq1d
    imbi2d
    ralbidva
    bitrd
    rexbidv
    ralbidv
    anbi2d
    3bitr2d
end
