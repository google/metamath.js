include "cgic.mm"
include "wbr.mm"
include "cv.mm"
include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "cgrp.mm"
include "c0.mm"
include "wne.mm"
include "brgic.mm"
include "n0.mm"
include "bitri.mm"
include "cghm.mm"
include "gimghm.mm"
include "ghmgrp2.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gicrcl
  let cR: class R
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let cC: class C
  let vg: setvar g
  let cT: class T


  assert |- ( R ~=g S -> S e. Grp )

  proof
    cR
    cS
    cgic
    wbr
    #
    vf
    cv
    #
    cR
    cS
    cgim
    co
    #
    wcel
    #
    vf
    wex
    #
    cS
    cgrp
    wcel
    #
    @0
    @2
    c0
    wne
    @4
    cR
    cS
    brgic
    vf
    @2
    n0
    bitri
    @3
    @5
    vf
    @3
    @1
    cR
    cS
    cghm
    co
    wcel
    @5
    cR
    cS
    @1
    gimghm
    cR
    cS
    @1
    ghmgrp2
    syl
    exlimiv
    sylbi
end
