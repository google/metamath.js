include "ccyg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cbs.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "iscyg.mm"
include "simplbi.mm"

theorem cyggrp
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cH: class H


  assert |- ( G e. CycGrp -> G e. Grp )

  proof
    cG
    ccyg
    wcel
    cG
    cgrp
    wcel
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
    cG
    cbs
    cfv
    #
    wceq
    vx
    @1
    wrex
    vx
    @1
    @0
    vn
    cG
    @1
    eqid
    @0
    eqid
    iscyg
    simplbi
end
