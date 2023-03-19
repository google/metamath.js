include "clmic.mm"
include "wbr.mm"
include "cv.mm"
include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "clmod.mm"
include "c0.mm"
include "wne.mm"
include "brlmic.mm"
include "n0.mm"
include "bitri.mm"
include "clmhm.mm"
include "lmimlmhm.mm"
include "lmhmlmod1.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem lmiclcl
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F


  assert |- ( R ~=m S -> R e. LMod )

  proof
    cR
    cS
    clmic
    wbr
    #
    vf
    cv
    #
    cR
    cS
    clmim
    co
    #
    wcel
    #
    vf
    wex
    #
    cR
    clmod
    wcel
    #
    @0
    @2
    c0
    wne
    @4
    cR
    cS
    brlmic
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
    clmhm
    co
    wcel
    @5
    cR
    cS
    @1
    lmimlmhm
    cR
    cS
    @1
    lmhmlmod1
    syl
    exlimiv
    sylbi
end
