include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cpolN.mm"
include "cdif.mm"
include "cmpt.mm"
include "watfvalN.mm"
include "fveq1d.mm"
include "wceq.mm"
include "sneq.mm"
include "fveq2d.mm"
include "difeq2d.mm"
include "eqid.mm"
include "cvv.mm"
include "catm.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem watvalN
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cK: class K
  let cW: class W
  let vd: setvar d
  let vk: setvar k
  assume watomfval.a: |- A = ( Atoms ` K )
  assume watomfval.p: |- P = ( _|_P ` K )
  assume watomfval.w: |- W = ( WAtoms ` K )


  assert |- ( ( K e. B /\ D e. A ) -> ( W ` D ) = ( A \ ( ( _|_P ` K ) ` { D } ) ) )

  proof
    cK
    cB
    wcel
    #
    cD
    cA
    wcel
    cD
    cW
    cfv
    cD
    vd
    cA
    cA
    vd
    cv
    #
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
    cfv
    cA
    cD
    csn
    #
    @3
    cfv
    #
    cdif
    #
    @0
    cD
    cW
    @6
    cA
    cB
    cP
    cK
    cW
    vd
    watomfval.a
    watomfval.p
    watomfval.w
    watfvalN
    fveq1d
    vd
    cD
    @5
    @9
    cA
    @6
    @1
    cD
    wceq
    #
    @4
    @8
    cA
    @10
    @2
    @7
    @3
    @1
    cD
    sneq
    fveq2d
    difeq2d
    @6
    eqid
    cA
    cvv
    wcel
    @9
    cvv
    wcel
    cA
    cK
    catm
    cfv
    cvv
    watomfval.a
    cK
    catm
    fvex
    eqeltri
    cA
    @8
    cvv
    difexg
    ax-mp
    fvmpt
    sylan9eq
end
