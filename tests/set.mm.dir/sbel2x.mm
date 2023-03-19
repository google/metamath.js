include "weq.mm"
include "wa.mm"
include "wsb.mm"
include "wex.mm"
include "nfv.mm"
include "2sb5rf.mm"
include "ancom.mm"
include "anbi1i.mm"
include "2exbii.mm"
include "excom.mm"
include "3bitri.mm"

theorem sbel2x
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint ph x
  disjoint ph y
  assert |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\ [ y / w ] [ x / z ] ph ) )

  proof
    wph
    vy
    vw
    weq
    #
    vx
    vz
    weq
    #
    wa
    #
    wph
    vz
    vx
    wsb
    vw
    vy
    wsb
    #
    wa
    #
    vx
    wex
    vy
    wex
    @1
    @0
    wa
    #
    @3
    wa
    #
    vx
    wex
    vy
    wex
    @6
    vy
    wex
    vx
    wex
    wph
    vw
    vz
    vy
    vx
    wph
    vy
    nfv
    wph
    vx
    nfv
    2sb5rf
    @4
    @6
    vy
    vx
    @2
    @5
    @3
    @0
    @1
    ancom
    anbi1i
    2exbii
    @6
    vy
    vx
    excom
    3bitri
end
