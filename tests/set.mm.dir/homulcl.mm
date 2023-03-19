include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "wa.mm"
include "chot.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csm.mm"
include "cmpt.mm"
include "ffvelrn.mm"
include "hvmulcl.mm"
include "sylan2.mm"
include "anassrs.mm"
include "eqid.mm"
include "fmptd.mm"
include "hommval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem homulcl
  let cA: class A
  let cT: class T
  let vx: setvar x
  let cS: class S


  assert |- ( ( A e. CC /\ T : ~H --> ~H ) -> ( A .op T ) : ~H --> ~H )

  proof
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    chil
    chil
    cA
    cT
    chot
    co
    #
    wf
    chil
    chil
    vx
    chil
    cA
    vx
    cv
    #
    cT
    cfv
    #
    csm
    co
    #
    cmpt
    #
    wf
    @2
    vx
    chil
    @6
    chil
    @7
    @0
    @1
    @4
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @1
    @8
    wa
    @0
    @5
    chil
    wcel
    @9
    chil
    chil
    @4
    cT
    ffvelrn
    cA
    @5
    hvmulcl
    sylan2
    anassrs
    @7
    eqid
    fmptd
    @2
    chil
    chil
    @3
    @7
    vx
    cA
    cT
    hommval
    feq1d
    mpbird
end
