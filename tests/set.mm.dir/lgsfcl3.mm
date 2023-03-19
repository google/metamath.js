include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
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
include "cmpt.mm"
include "wf.mm"
include "eqid.mm"
include "lgsfcl.mm"
include "clgs.mm"
include "lgsval4lem.mm"
include "syl6eqr.mm"
include "feq1d.mm"
include "mpbid.mm"

theorem lgsfcl3
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  assume lgsval4.1: |- F = ( n e. NN |-> if ( n e. Prime , ( ( A /L n ) ^ ( n pCnt N ) ) , 1 ) )

  disjoint A n
  disjoint N n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint P n
  assert |- ( ( A e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> F : NN --> ZZ )

  proof
    cA
    cz
    wcel
    cN
    cz
    wcel
    cN
    cc0
    wne
    w3a
    #
    cn
    cz
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    @1
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
    cA
    @1
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
    @1
    cmo
    co
    c1
    cmin
    co
    cif
    @1
    cN
    cpc
    co
    #
    cexp
    co
    c1
    cif
    cmpt
    #
    wf
    cn
    cz
    cF
    wf
    cA
    vn
    @4
    cN
    @4
    eqid
    #
    lgsfcl
    @0
    cn
    cz
    @4
    cF
    @0
    @4
    vn
    cn
    @2
    cA
    @1
    clgs
    co
    @3
    cexp
    co
    c1
    cif
    cmpt
    cF
    cA
    vn
    @4
    cN
    @5
    lgsval4lem
    lgsval4.1
    syl6eqr
    feq1d
    mpbid
end
