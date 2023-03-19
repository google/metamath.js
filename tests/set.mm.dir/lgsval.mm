include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cn.mm"
include "cprime.mm"
include "wcel.mm"
include "cdvds.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "cpc.mm"
include "cmpt.mm"
include "cseq.mm"
include "clgs.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "ifbid.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "breq2d.mm"
include "eleq1d.mm"
include "ifbieq2d.mm"
include "ifeq12d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifeq1d.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "ifbieq12d.mm"
include "df-lgs.mm"
include "cn0.mm"
include "1nn0.mm"
include "0nn0.mm"
include "keepel.mm"
include "elexi.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem lgsval
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cZ: class Z
  assume lgsval.1: |- F = ( n e. NN |-> if ( n e. Prime , ( if ( n = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( n - 1 ) / 2 ) ) + 1 ) mod n ) - 1 ) ) ^ ( n pCnt N ) ) , 1 ) )

  disjoint A n
  disjoint N n
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F a
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint M n
  disjoint M x
  disjoint N a
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Z a
  disjoint Z b
  disjoint Z n
  disjoint Z y
  disjoint Z z
  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( A /L N ) = if ( N = 0 , if ( ( A ^ 2 ) = 1 , 1 , 0 ) , ( if ( ( N < 0 /\ A < 0 ) , -u 1 , 1 ) x. ( seq 1 ( x. , F ) ` ( abs ` N ) ) ) ) )

  proof
    va
    vm
    cA
    cN
    cz
    cz
    vm
    cv
    #
    cc0
    wceq
    #
    va
    cv
    #
    c2
    cexp
    co
    #
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    @0
    cc0
    clt
    wbr
    #
    @2
    cc0
    clt
    wbr
    #
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    @0
    cabs
    cfv
    #
    cmul
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    @12
    c2
    wceq
    #
    c2
    @2
    cdvds
    wbr
    #
    cc0
    @2
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    wcel
    #
    c1
    @9
    cif
    #
    cif
    #
    @2
    @12
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    @12
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @12
    @0
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    cif
    cN
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    #
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    cN
    cc0
    clt
    wbr
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    @9
    c1
    cif
    #
    cN
    cabs
    cfv
    #
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    cif
    clgs
    @2
    cA
    wceq
    #
    @0
    cN
    wceq
    #
    wa
    #
    @1
    @34
    @5
    @33
    @37
    @45
    @48
    @0
    cN
    cc0
    @46
    @47
    simpr
    #
    eqeq1d
    @48
    @4
    @36
    c1
    cc0
    @48
    @3
    @35
    c1
    @48
    @2
    cA
    c2
    cexp
    @46
    @47
    simpl
    #
    oveq1d
    eqeq1d
    ifbid
    @48
    @10
    @41
    @32
    @44
    cmul
    @48
    @8
    @40
    @9
    c1
    @48
    @6
    @38
    @7
    @39
    @48
    @0
    cN
    cc0
    clt
    @49
    breq1d
    @48
    @2
    cA
    cc0
    clt
    @50
    breq1d
    anbi12d
    ifbid
    @48
    @11
    @42
    @31
    @43
    @48
    @30
    cF
    cmul
    c1
    @48
    @30
    vn
    cn
    @13
    @14
    c2
    cA
    cdvds
    wbr
    #
    cc0
    cA
    c8
    cmo
    co
    #
    @17
    wcel
    #
    c1
    @9
    cif
    #
    cif
    #
    cA
    @21
    cexp
    co
    #
    c1
    caddc
    co
    #
    @12
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @12
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    cF
    @48
    vn
    cn
    @29
    @63
    @48
    @13
    @28
    @62
    c1
    @48
    @26
    @60
    @27
    @61
    cexp
    @48
    @14
    @20
    @55
    @25
    @59
    @48
    @15
    @51
    @19
    @54
    cc0
    @48
    @2
    cA
    c2
    cdvds
    @50
    breq2d
    @48
    @18
    @53
    c1
    @9
    @48
    @16
    @52
    @17
    @48
    @2
    cA
    c8
    cmo
    @50
    oveq1d
    eleq1d
    ifbid
    ifbieq2d
    @48
    @24
    @58
    c1
    cmin
    @48
    @23
    @57
    @12
    cmo
    @48
    @22
    @56
    c1
    caddc
    @48
    @2
    cA
    @21
    cexp
    @50
    oveq1d
    oveq1d
    oveq1d
    oveq1d
    ifeq12d
    @48
    @0
    cN
    @12
    cpc
    @49
    oveq2d
    oveq12d
    ifeq1d
    mpteq2dv
    lgsval.1
    syl6eqr
    seqeq3d
    @48
    @0
    cN
    cabs
    @49
    fveq2d
    fveq12d
    oveq12d
    ifbieq12d
    vn
    vm
    va
    df-lgs
    @34
    @37
    @45
    @37
    cn0
    @36
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    elexi
    @41
    @44
    cmul
    ovex
    ifex
    ovmpt2a
end
