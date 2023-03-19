include "chmph.mm"
include "wbr.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "hmph.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "hmeoco.mm"
include "hmphi.mm"
include "syl.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem hmphtr
  let cJ: class J
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( J ~= K /\ K ~= L ) -> J ~= L )

  proof
    cJ
    cK
    chmph
    wbr
    cJ
    cK
    chmeo
    co
    #
    c0
    wne
    #
    cK
    cL
    chmeo
    co
    #
    c0
    wne
    #
    cJ
    cL
    chmph
    wbr
    #
    cK
    cL
    chmph
    wbr
    cJ
    cK
    hmph
    cK
    cL
    hmph
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
    @11
    @8
    @5
    ccom
    #
    cJ
    cL
    chmeo
    co
    wcel
    @4
    @5
    @8
    cJ
    cK
    cL
    hmeoco
    @12
    cJ
    cL
    hmphi
    syl
    exlimivv
    sylbir
    syl2anb
    syl2anb
end
