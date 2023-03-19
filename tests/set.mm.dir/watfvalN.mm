include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cpolN.mm"
include "cfv.mm"
include "cdif.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cwpointsN.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "difeq12d.mm"
include "mpteq12dv.mm"
include "df-watsN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem watfvalN
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let cW: class W
  let vd: setvar d
  let vk: setvar k
  let cD: class D
  assume watomfval.a: |- A = ( Atoms ` K )
  assume watomfval.p: |- P = ( _|_P ` K )
  assume watomfval.w: |- W = ( WAtoms ` K )

  disjoint A d
  disjoint K d
  disjoint d k
  disjoint A k
  disjoint D d
  disjoint K k
  assert |- ( K e. B -> W = ( d e. A |-> ( A \ ( ( _|_P ` K ) ` { d } ) ) ) )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cW
    vd
    cA
    cA
    vd
    cv
    csn
    #
    cK
    cpolN
    cfv
    #
    cfv
    #
    cdif
    #
    cmpt
    #
    wceq
    cK
    cB
    elex
    @0
    cW
    cK
    cwpointsN
    cfv
    @5
    watomfval.w
    vk
    cK
    vd
    vk
    cv
    #
    catm
    cfv
    #
    @7
    @1
    @6
    cpolN
    cfv
    #
    cfv
    #
    cdif
    #
    cmpt
    @5
    cvv
    cwpointsN
    @6
    cK
    wceq
    #
    vd
    @7
    @10
    cA
    @4
    @11
    @7
    cK
    catm
    cfv
    #
    cA
    @6
    cK
    catm
    fveq2
    watomfval.a
    syl6eqr
    #
    @11
    @7
    cA
    @9
    @3
    @13
    @11
    @1
    @8
    @2
    @6
    cK
    cpolN
    fveq2
    fveq1d
    difeq12d
    mpteq12dv
    vk
    vd
    df-watsN
    vd
    cA
    @4
    cA
    @12
    cvv
    watomfval.a
    cK
    catm
    fvex
    eqeltri
    mptex
    fvmpt
    syl5eq
    syl
end
