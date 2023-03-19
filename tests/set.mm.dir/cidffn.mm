include "ccat.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "chom.mm"
include "cco.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "csb.mm"
include "ccid.mm"
include "vex.mm"
include "mptex.mm"
include "csbex.mm"
include "df-cid.mm"
include "fnmpti.mm"

theorem cidffn
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C


  assert |- Id Fn Cat

  proof
    vc
    ccat
    vb
    vc
    cv
    #
    cbs
    cfv
    #
    vh
    @0
    chom
    cfv
    #
    vo
    @0
    cco
    cfv
    #
    vx
    vb
    cv
    #
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    @8
    vo
    cv
    #
    co
    co
    @6
    wceq
    vf
    @7
    @8
    vh
    cv
    #
    co
    wral
    @6
    @5
    @8
    @8
    cop
    @7
    @9
    co
    co
    @6
    wceq
    vf
    @8
    @7
    @10
    co
    wral
    wa
    vy
    @4
    wral
    vg
    @8
    @8
    @10
    co
    crio
    #
    cmpt
    #
    csb
    #
    csb
    #
    csb
    ccid
    vb
    @1
    @14
    vh
    @2
    @13
    vo
    @3
    @12
    vx
    @4
    @11
    vb
    vex
    mptex
    csbex
    csbex
    csbex
    vx
    vy
    vf
    vg
    vh
    vo
    vb
    vc
    df-cid
    fnmpti
end
