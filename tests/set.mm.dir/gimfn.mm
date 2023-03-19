include "cgrp.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cghm.mm"
include "co.mm"
include "crab.mm"
include "cgim.mm"
include "df-gim.mm"
include "ovex.mm"
include "rabex.mm"
include "fnmpt2i.mm"

theorem gimfn
  let vg: setvar g
  let vs: setvar s
  let vt: setvar t


  assert |- GrpIso Fn ( Grp X. Grp )

  proof
    vs
    vt
    cgrp
    cgrp
    vs
    cv
    #
    cbs
    cfv
    vt
    cv
    #
    cbs
    cfv
    vg
    cv
    wf1o
    #
    vg
    @0
    @1
    cghm
    co
    #
    crab
    cgim
    vt
    vg
    vs
    df-gim
    @2
    vg
    @3
    @0
    @1
    cghm
    ovex
    rabex
    fnmpt2i
end
