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
include "wi.mm"
include "wa.mm"
include "ccom.mm"
include "lmimco.mm"
include "brlmici.mm"
include "syl.mm"
include "ex.mm"
include "exlimiv.mm"
include "com12.mm"
include "imp.mm"
include "syl2anb.mm"

theorem lmictra
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( R ~=m S /\ S ~=m T ) -> R ~=m T )

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
    cT
    clmim
    co
    #
    c0
    wne
    #
    cR
    cT
    clmic
    wbr
    #
    cS
    cT
    clmic
    wbr
    cR
    cS
    brlmic
    cS
    cT
    brlmic
    @1
    vg
    cv
    #
    @0
    wcel
    #
    vg
    wex
    #
    vf
    cv
    #
    @2
    wcel
    #
    vf
    wex
    #
    @4
    @3
    vg
    @0
    n0
    vf
    @2
    n0
    @7
    @10
    @4
    @6
    @10
    @4
    wi
    vg
    @10
    @6
    @4
    @9
    @6
    @4
    wi
    vf
    @9
    @6
    @4
    @9
    @6
    wa
    @8
    @5
    ccom
    #
    cR
    cT
    clmim
    co
    wcel
    @4
    cR
    cS
    cT
    @8
    @5
    lmimco
    cR
    cT
    @11
    brlmici
    syl
    ex
    exlimiv
    com12
    exlimiv
    imp
    syl2anb
    syl2anb
end
