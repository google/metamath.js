include "cv.mm"
include "wss.mm"
include "cdm.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "sseq2.mm"
include "dmeq.mm"
include "fneq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "ac7.mm"
include "vtoclg.mm"

theorem ac7g
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vx: setvar x

  disjoint R f
  disjoint f x
  disjoint R x
  assert |- ( R e. A -> E. f ( f C_ R /\ f Fn dom R ) )

  proof
    vf
    cv
    #
    vx
    cv
    #
    wss
    #
    @0
    @1
    cdm
    #
    wfn
    #
    wa
    #
    vf
    wex
    @0
    cR
    wss
    #
    @0
    cR
    cdm
    #
    wfn
    #
    wa
    #
    vf
    wex
    vx
    cR
    cA
    @1
    cR
    wceq
    #
    @5
    @9
    vf
    @10
    @2
    @6
    @4
    @8
    @1
    cR
    @0
    sseq2
    @10
    @3
    @7
    @0
    @1
    cR
    dmeq
    fneq2d
    anbi12d
    exbidv
    vx
    vf
    ac7
    vtoclg
end
