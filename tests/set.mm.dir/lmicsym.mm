include "clmic.mm"
include "wbr.mm"
include "clmim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "brlmic.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "ccnv.mm"
include "lmimcnv.mm"
include "brlmici.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem lmicsym
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F


  assert |- ( R ~=m S -> S ~=m R )

  proof
    cR
    cS
    clmic
    wbr
    cR
    cS
    clmim
    co
    #
    c0
    wne
    #
    cS
    cR
    clmic
    wbr
    #
    cR
    cS
    brlmic
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
    clmim
    co
    wcel
    @2
    cR
    cS
    @3
    lmimcnv
    cS
    cR
    @5
    brlmici
    syl
    exlimiv
    sylbi
    sylbi
end
