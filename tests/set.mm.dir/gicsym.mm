include "cgic.mm"
include "wbr.mm"
include "cgim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "brgic.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "ccnv.mm"
include "gimcnv.mm"
include "brgici.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gicsym
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


  assert |- ( R ~=g S -> S ~=g R )

  proof
    cR
    cS
    cgic
    wbr
    cR
    cS
    cgim
    co
    #
    c0
    wne
    #
    cS
    cR
    cgic
    wbr
    #
    cR
    cS
    brgic
    @1
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    n0
    @4
    @2
    vf
    @4
    @3
    ccnv
    #
    cS
    cR
    cgim
    co
    wcel
    @2
    cR
    cS
    @3
    gimcnv
    cS
    cR
    @5
    brgici
    syl
    exlimiv
    sylbi
    sylbi
end
