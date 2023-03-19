include "ccyg.mm"
include "wcel.mm"
include "cv.mm"
include "cz.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "crab.mm"
include "cgic.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cgrp.mm"
include "eqid.mm"
include "iscyg2.mm"
include "simprbi.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "czrh.mm"
include "cop.mm"
include "simpl.mm"
include "simpr.mm"
include "cygznlem3.mm"
include "exlimddv.mm"

theorem cygzn
  let cB: class B
  let cG: class G
  let cN: class N
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cE: class E
  let cM: class M
  let c.x: class .x.
  let cL: class L
  let wph: wff ph
  let cF: class F
  let cX: class X
  assume cygzn.b: |- B = ( Base ` G )
  assume cygzn.n: |- N = if ( B e. Fin , ( # ` B ) , 0 )
  assume cygzn.y: |- Y = ( Z/nZ ` N )


  assert |- ( G e. CycGrp -> G ~=g Y )

  proof
    cG
    ccyg
    wcel
    #
    vg
    cv
    #
    vn
    cz
    vn
    cv
    vx
    cv
    cG
    cmg
    cfv
    #
    co
    cmpt
    crn
    cB
    wceq
    vx
    cB
    crab
    #
    wcel
    #
    cG
    cY
    cgic
    wbr
    vg
    @0
    @3
    c0
    wne
    #
    @4
    vg
    wex
    @0
    cG
    cgrp
    wcel
    @5
    vx
    cB
    @2
    vn
    @3
    cG
    cygzn.b
    @2
    eqid
    #
    @3
    eqid
    #
    iscyg2
    simprbi
    vg
    @3
    n0
    sylib
    @0
    @4
    wa
    vx
    cB
    @2
    vm
    vn
    @3
    vm
    cz
    vm
    cv
    #
    cY
    czrh
    cfv
    #
    cfv
    @8
    @1
    @2
    co
    cop
    cmpt
    crn
    #
    cG
    @9
    cN
    @1
    cY
    cygzn.b
    cygzn.n
    cygzn.y
    @6
    @9
    eqid
    @7
    @0
    @4
    simpl
    @0
    @4
    simpr
    @10
    eqid
    cygznlem3
    exlimddv
end
