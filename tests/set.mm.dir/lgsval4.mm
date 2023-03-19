include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
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
include "cv.mm"
include "cprime.mm"
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
include "eqid.mm"
include "lgsval.mm"
include "3adant3.mm"
include "simp3.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "lgsval4lem.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem lgsval4
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
  assert |- ( ( A e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( A /L N ) = ( if ( ( N < 0 /\ A < 0 ) , -u 1 , 1 ) x. ( seq 1 ( x. , F ) ` ( abs ` N ) ) ) )

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
    cA
    cN
    clgs
    co
    #
    cN
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    c1
    wceq
    c1
    cc0
    cif
    #
    cN
    cc0
    clt
    wbr
    cA
    cc0
    clt
    wbr
    wa
    c1
    cneg
    #
    c1
    cif
    #
    cN
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
    @10
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
    @7
    cif
    cif
    cA
    @10
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
    @10
    cmo
    co
    c1
    cmin
    co
    cif
    @10
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
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    #
    cif
    #
    @16
    @8
    @9
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    cmul
    co
    @0
    @1
    @4
    @17
    wceq
    @2
    cA
    vn
    @13
    cN
    @13
    eqid
    #
    lgsval
    3adant3
    @3
    @5
    @6
    @16
    @3
    cN
    cc0
    @0
    @1
    @2
    simp3
    neneqd
    iffalsed
    @3
    @15
    @19
    @8
    cmul
    @3
    @9
    @14
    @18
    @3
    @13
    cF
    cmul
    c1
    @3
    @13
    vn
    cn
    @11
    cA
    @10
    clgs
    co
    @12
    cexp
    co
    c1
    cif
    cmpt
    cF
    cA
    vn
    @13
    cN
    @20
    lgsval4lem
    lgsval4.1
    syl6eqr
    seqeq3d
    fveq1d
    oveq2d
    3eqtrd
end
