include "ccat.mm"
include "wcel.mm"
include "wfn.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "chom.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "riotaex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "id.mm"
include "cidfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem cidfn
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  assume cidfn.b: |- B = ( Base ` C )
  assume cidfn.i: |- .1. = ( Id ` C )


  assert |- ( C e. Cat -> .1. Fn B )

  proof
    cC
    ccat
    wcel
    #
    c.1
    cB
    wfn
    vx
    cB
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
    @4
    cC
    cco
    cfv
    #
    co
    co
    @2
    wceq
    vf
    @3
    @4
    cC
    chom
    cfv
    #
    co
    wral
    @2
    @1
    @4
    @4
    cop
    @3
    @5
    co
    co
    @2
    wceq
    vf
    @4
    @3
    @6
    co
    wral
    wa
    vy
    cB
    wral
    #
    vg
    @4
    @4
    @6
    co
    #
    crio
    #
    cmpt
    #
    cB
    wfn
    vx
    cB
    @9
    @10
    @7
    vg
    @8
    riotaex
    @10
    eqid
    fnmpti
    @0
    cB
    c.1
    @10
    @0
    vx
    vy
    cB
    cC
    @5
    c.1
    vf
    vg
    @6
    cidfn.b
    @6
    eqid
    @5
    eqid
    @0
    id
    cidfn.i
    cidfval
    fneq1d
    mpbiri
end
