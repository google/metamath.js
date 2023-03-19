include "cn.mm"
include "wss.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cpw.mm"
include "wceq.mm"
include "nnex.mm"
include "elpw2.mm"
include "eleq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylbir.mm"
include "fveq1d.mm"
include "eleq1.mm"
include "oveq2.mm"
include "ifbieq1d.mm"
include "eqid.mm"
include "ovex.mm"
include "c0ex.mm"
include "ifex.mm"
include "sylan9eq.mm"

theorem rpnnen2lem1
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cM: class M
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint N n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint M x
  assert |- ( ( A C_ NN /\ N e. NN ) -> ( ( F ` A ) ` N ) = if ( N e. A , ( ( 1 / 3 ) ^ N ) , 0 ) )

  proof
    cA
    cn
    wss
    #
    cN
    cn
    wcel
    cN
    cA
    cF
    cfv
    #
    cfv
    cN
    vn
    cn
    vn
    cv
    #
    cA
    wcel
    #
    c1
    c3
    cdiv
    co
    #
    @2
    cexp
    co
    #
    cc0
    cif
    #
    cmpt
    #
    cfv
    cN
    cA
    wcel
    #
    @4
    cN
    cexp
    co
    #
    cc0
    cif
    #
    @0
    cN
    @1
    @7
    @0
    cA
    cn
    cpw
    #
    wcel
    @1
    @7
    wceq
    cA
    cn
    nnex
    elpw2
    vx
    cA
    vn
    cn
    @2
    vx
    cv
    #
    wcel
    #
    @5
    cc0
    cif
    #
    cmpt
    @7
    @11
    cF
    @12
    cA
    wceq
    #
    vn
    cn
    @14
    @6
    @15
    @13
    @3
    @5
    cc0
    @12
    cA
    @2
    eleq2
    ifbid
    mpteq2dv
    rpnnen2.1
    vn
    cn
    @6
    nnex
    mptex
    fvmpt
    sylbir
    fveq1d
    vn
    cN
    @6
    @10
    cn
    @7
    @2
    cN
    wceq
    @3
    @8
    @5
    @9
    cc0
    @2
    cN
    cA
    eleq1
    @2
    cN
    @4
    cexp
    oveq2
    ifbieq1d
    @7
    eqid
    @8
    @9
    cc0
    @4
    cN
    cexp
    ovex
    c0ex
    ifex
    fvmpt
    sylan9eq
end
