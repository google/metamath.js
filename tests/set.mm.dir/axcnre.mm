include "cv.mm"
include "cop.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cr.mm"
include "wrex.mm"
include "cnr.mm"
include "cc.mm"
include "df-c.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "c0r.mm"
include "opelreal.mm"
include "anbi12i.mm"
include "biimpri.mm"
include "cplr.mm"
include "c1r.mm"
include "df-i.mm"
include "oveq1i.mm"
include "cmr.mm"
include "cm1r.mm"
include "0r.mm"
include "1sr.mm"
include "mulcnsr.mm"
include "mpanl12.mm"
include "mpan2.mm"
include "mulcomsr.mm"
include "00sr.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "m1r.mm"
include "eqtri.mm"
include "0idsr.mm"
include "syl6eq.mm"
include "1idsr.mm"
include "eqtrd.mm"
include "opeq12d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "addcnsr.mm"
include "mpanl2.mm"
include "mpanr1.mm"
include "addcomsr.mm"
include "opeq12.mm"
include "syl2an.mm"
include "3eqtrrd.mm"
include "opex.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq1.mm"
include "oveq2.mm"
include "sylan9eq.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spc2ev.mm"
include "syl2anc.mm"
include "r2ex.mm"
include "sylibr.mm"
include "optocl.mm"

theorem axcnre
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( A e. CC -> E. x e. RR E. y e. RR A = ( x + ( _i x. y ) ) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    #
    cA
    @6
    wceq
    #
    vy
    cr
    wrex
    vx
    cr
    wrex
    vz
    vw
    cA
    cnr
    cnr
    cc
    df-c
    @2
    cA
    wceq
    @7
    @9
    vx
    vy
    cr
    cr
    @2
    cA
    @6
    eqeq1
    2rexbidv
    @0
    cnr
    wcel
    #
    @1
    cnr
    wcel
    #
    wa
    #
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    #
    @7
    wa
    #
    vy
    wex
    vx
    wex
    #
    @8
    @12
    @0
    c0r
    cop
    #
    cr
    wcel
    #
    @1
    c0r
    cop
    #
    cr
    wcel
    #
    wa
    #
    @2
    @18
    ci
    @20
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @17
    @22
    @12
    @19
    @10
    @21
    @11
    @0
    opelreal
    @1
    opelreal
    anbi12i
    biimpri
    @12
    @24
    @18
    c0r
    @1
    cop
    #
    caddc
    co
    #
    @0
    c0r
    cplr
    co
    #
    c0r
    @1
    cplr
    co
    #
    cop
    #
    @2
    @11
    @24
    @27
    wceq
    @10
    @11
    @23
    @26
    @18
    caddc
    @11
    @23
    c0r
    c1r
    cop
    #
    @20
    cmul
    co
    #
    @26
    ci
    @31
    @20
    cmul
    df-i
    oveq1i
    @11
    @32
    c0r
    @1
    cmr
    co
    #
    cm1r
    c1r
    c0r
    cmr
    co
    #
    cmr
    co
    #
    cplr
    co
    #
    c1r
    @1
    cmr
    co
    #
    c0r
    c0r
    cmr
    co
    #
    cplr
    co
    #
    cop
    #
    @26
    @11
    c0r
    cnr
    wcel
    #
    @32
    @40
    wceq
    #
    0r
    @41
    c1r
    cnr
    wcel
    #
    @11
    @41
    wa
    @42
    0r
    1sr
    c0r
    c1r
    @1
    c0r
    mulcnsr
    mpanl12
    mpan2
    @11
    @36
    c0r
    @39
    @1
    @11
    @36
    c0r
    @35
    cplr
    co
    #
    c0r
    @11
    @33
    c0r
    @35
    cplr
    @11
    @33
    @1
    c0r
    cmr
    co
    c0r
    c0r
    @1
    mulcomsr
    @1
    00sr
    syl5eq
    oveq1d
    @44
    c0r
    c0r
    cplr
    co
    #
    c0r
    @35
    c0r
    c0r
    cplr
    @35
    cm1r
    c0r
    cmr
    co
    #
    c0r
    @34
    c0r
    cm1r
    cmr
    @43
    @34
    c0r
    wceq
    1sr
    c1r
    00sr
    ax-mp
    oveq2i
    cm1r
    cnr
    wcel
    @46
    c0r
    wceq
    m1r
    cm1r
    00sr
    ax-mp
    eqtri
    oveq2i
    @41
    @45
    c0r
    wceq
    0r
    c0r
    0idsr
    ax-mp
    eqtri
    syl6eq
    @11
    @39
    @1
    @38
    cplr
    co
    #
    @1
    @11
    @37
    @1
    @38
    cplr
    @11
    @37
    @1
    c1r
    cmr
    co
    @1
    c1r
    @1
    mulcomsr
    @1
    1idsr
    syl5eq
    oveq1d
    @11
    @47
    @1
    c0r
    cplr
    co
    #
    @1
    @38
    c0r
    @1
    cplr
    @41
    @38
    c0r
    wceq
    0r
    c0r
    00sr
    ax-mp
    oveq2i
    @1
    0idsr
    #
    syl5eq
    eqtrd
    opeq12d
    eqtrd
    syl5eq
    oveq2d
    adantl
    @10
    @41
    @11
    @27
    @30
    wceq
    #
    0r
    @10
    @41
    @41
    @11
    wa
    @50
    0r
    @0
    c0r
    c0r
    @1
    addcnsr
    mpanl2
    mpanr1
    @10
    @28
    @0
    wceq
    @29
    @1
    wceq
    @30
    @2
    wceq
    @11
    @0
    0idsr
    @11
    @29
    @48
    @1
    c0r
    @1
    addcomsr
    @49
    syl5eq
    @28
    @29
    @0
    @1
    opeq12
    syl2an
    3eqtrrd
    @16
    @22
    @25
    wa
    vx
    vy
    @18
    @20
    @0
    c0r
    opex
    @1
    c0r
    opex
    @3
    @18
    wceq
    #
    @4
    @20
    wceq
    #
    wa
    #
    @15
    @22
    @7
    @25
    @51
    @13
    @19
    @52
    @14
    @21
    @3
    @18
    cr
    eleq1
    @4
    @20
    cr
    eleq1
    bi2anan9
    @53
    @6
    @24
    @2
    @51
    @52
    @6
    @18
    @5
    caddc
    co
    @24
    @3
    @18
    @5
    caddc
    oveq1
    @52
    @5
    @23
    @18
    caddc
    @4
    @20
    ci
    cmul
    oveq2
    oveq2d
    sylan9eq
    eqeq2d
    anbi12d
    spc2ev
    syl2anc
    @7
    vx
    vy
    cr
    cr
    r2ex
    sylibr
    optocl
end
