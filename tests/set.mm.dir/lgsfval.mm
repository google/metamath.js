include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cpc.mm"
include "cn.mm"
include "eleq1.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "ifbieq1d.mm"
include "ovex.mm"
include "1ex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem lgsfval
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cZ: class Z
  assume lgsval.1: |- F = ( n e. NN |-> if ( n e. Prime , ( if ( n = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( n - 1 ) / 2 ) ) + 1 ) mod n ) - 1 ) ) ^ ( n pCnt N ) ) , 1 ) )

  disjoint A n
  disjoint M n
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
  assert |- ( M e. NN -> ( F ` M ) = if ( M e. Prime , ( if ( M = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( M - 1 ) / 2 ) ) + 1 ) mod M ) - 1 ) ) ^ ( M pCnt N ) ) , 1 ) )

  proof
    vn
    cM
    vn
    cv
    #
    cprime
    wcel
    #
    @0
    c2
    wceq
    #
    c2
    cA
    cdvds
    wbr
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    c1
    c1
    cneg
    cif
    cif
    #
    cA
    @0
    c1
    cmin
    co
    #
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
    @0
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    @0
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    cM
    cprime
    wcel
    #
    cM
    c2
    wceq
    #
    @3
    cA
    cM
    c1
    cmin
    co
    #
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
    cM
    cmo
    co
    #
    c1
    cmin
    co
    #
    cif
    #
    cM
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    cn
    cF
    @0
    cM
    wceq
    #
    @1
    @13
    @12
    @23
    c1
    @0
    cM
    cprime
    eleq1
    @24
    @10
    @21
    @11
    @22
    cexp
    @24
    @2
    @14
    @9
    @20
    @3
    @0
    cM
    c2
    eqeq1
    @24
    @8
    @19
    c1
    cmin
    @24
    @7
    @18
    @0
    cM
    cmo
    @24
    @6
    @17
    c1
    caddc
    @24
    @5
    @16
    cA
    cexp
    @24
    @4
    @15
    c2
    cdiv
    @0
    cM
    c1
    cmin
    oveq1
    oveq1d
    oveq2d
    oveq1d
    @24
    id
    oveq12d
    oveq1d
    ifbieq2d
    @0
    cM
    cN
    cpc
    oveq1
    oveq12d
    ifbieq1d
    lgsval.1
    @13
    @23
    c1
    @21
    @22
    cexp
    ovex
    1ex
    ifex
    fvmpt
end
