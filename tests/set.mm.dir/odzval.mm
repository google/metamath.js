include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "codz.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wa.mm"
include "cmpt.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "cbvrabv.mm"
include "syl6eqr.mm"
include "breq1.mm"
include "infeq1d.mm"
include "mpteq12dv.mm"
include "df-odz.mm"
include "zex.mm"
include "mptrabex.mm"
include "fvmpt.mm"
include "fveq1d.mm"
include "elrab.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "eqid.mm"
include "ltso.mm"
include "infex.mm"
include "sylbir.mm"
include "sylan9eq.mm"
include "3impb.mm"

theorem odzval
  let cA: class A
  let vn: setvar n
  let cN: class N
  let vm: setvar m
  let vx: setvar x
  let cK: class K

  disjoint N n
  disjoint A n
  disjoint m n
  disjoint m x
  disjoint N m
  disjoint n x
  disjoint N x
  disjoint A x
  disjoint K n
  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( odZ ` N ) ` A ) = inf ( { n e. NN | N || ( ( A ^ n ) - 1 ) } , RR , < ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cN
    codz
    cfv
    #
    cfv
    #
    cN
    cA
    vn
    cv
    #
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    wceq
    @0
    @1
    @3
    wa
    #
    @5
    cA
    vx
    @6
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vn
    cz
    crab
    #
    cN
    vx
    cv
    #
    @6
    cexp
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    #
    cfv
    #
    @11
    @0
    cA
    @4
    @22
    vm
    cN
    vx
    @16
    vm
    cv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    cz
    crab
    #
    @24
    @18
    cdvds
    wbr
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    @22
    cn
    codz
    @24
    cN
    wceq
    #
    vx
    @27
    @30
    @15
    @21
    @31
    @27
    @16
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vx
    cz
    crab
    @15
    @31
    @26
    @33
    vx
    cz
    @31
    @25
    @32
    c1
    @24
    cN
    @16
    cgcd
    oveq2
    eqeq1d
    rabbidv
    @14
    @33
    vn
    vx
    cz
    @6
    @16
    wceq
    @13
    @32
    c1
    @6
    @16
    cN
    cgcd
    oveq1
    eqeq1d
    cbvrabv
    syl6eqr
    @31
    cr
    @29
    @20
    clt
    @31
    @28
    @19
    vn
    cn
    @24
    cN
    @18
    cdvds
    breq1
    rabbidv
    infeq1d
    mpteq12dv
    vx
    vn
    vm
    df-odz
    @14
    vx
    vn
    cz
    @21
    zex
    mptrabex
    fvmpt
    fveq1d
    @12
    cA
    @15
    wcel
    @23
    @11
    wceq
    @14
    @3
    vn
    cA
    cz
    @6
    cA
    wceq
    @13
    @2
    c1
    @6
    cA
    cN
    cgcd
    oveq1
    eqeq1d
    elrab
    vx
    cA
    @21
    @11
    @15
    @22
    @16
    cA
    wceq
    #
    cr
    @20
    @10
    clt
    @34
    @19
    @9
    vn
    cn
    @34
    @18
    @8
    cN
    cdvds
    @34
    @17
    @7
    c1
    cmin
    @16
    cA
    @6
    cexp
    oveq1
    oveq1d
    breq2d
    rabbidv
    infeq1d
    @22
    eqid
    cr
    @10
    clt
    ltso
    infex
    fvmpt
    sylbir
    sylan9eq
    3impb
end
