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
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "gimco.mm"
include "brgici.mm"
include "syl.mm"
include "ancoms.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem gictr
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vf: setvar f
  let cC: class C
  let vg: setvar g


  assert |- ( ( R ~=g S /\ S ~=g T ) -> R ~=g T )

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
    cT
    cgim
    co
    #
    c0
    wne
    #
    cR
    cT
    cgic
    wbr
    #
    cS
    cT
    cgic
    wbr
    cR
    cS
    brgic
    cS
    cT
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
    #
    vg
    cv
    #
    @2
    wcel
    #
    vg
    wex
    #
    @4
    @3
    vf
    @0
    n0
    vg
    @2
    n0
    @7
    @10
    wa
    @6
    @9
    wa
    #
    vg
    wex
    vf
    wex
    @4
    @6
    @9
    vf
    vg
    eeanv
    @11
    @4
    vf
    vg
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
    cgim
    co
    wcel
    @4
    cR
    cS
    cT
    @8
    @5
    gimco
    cR
    cT
    @12
    brgici
    syl
    ancoms
    exlimivv
    sylbir
    syl2anb
    syl2anb
end
