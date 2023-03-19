include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "clgs.mm"
include "co.mm"
include "cpc.mm"
include "cexp.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "c8.mm"
include "cmo.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "wa.mm"
include "eqid.mm"
include "lgsval2lem.mm"
include "3ad2antl1.mm"
include "oveq1d.mm"
include "ifeq1da.mm"
include "mpteq2dv.mm"
include "syl6reqr.mm"

theorem lgsval4lem
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
  assert |- ( ( A e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> F = ( n e. NN |-> if ( n e. Prime , ( ( A /L n ) ^ ( n pCnt N ) ) , 1 ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    #
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    cA
    @4
    clgs
    co
    #
    @4
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
    vn
    cn
    @5
    @4
    c2
    wceq
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
    @4
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    @4
    cmo
    co
    c1
    cmin
    co
    cif
    #
    @7
    cexp
    co
    #
    c1
    cif
    #
    cmpt
    cF
    @3
    vn
    cn
    @9
    @13
    @3
    @5
    @8
    @12
    c1
    @3
    @5
    wa
    @6
    @11
    @7
    cexp
    @0
    @1
    @5
    @6
    @11
    wceq
    @2
    cA
    vm
    vm
    cn
    vm
    cv
    #
    cprime
    wcel
    @14
    c2
    wceq
    @10
    cA
    @14
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    @14
    cmo
    co
    c1
    cmin
    co
    cif
    @14
    @4
    cpc
    co
    cexp
    co
    c1
    cif
    cmpt
    #
    @4
    @15
    eqid
    lgsval2lem
    3ad2antl1
    oveq1d
    ifeq1da
    mpteq2dv
    lgsval.1
    syl6reqr
end
