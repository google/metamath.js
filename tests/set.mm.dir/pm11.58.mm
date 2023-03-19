include "wsb.mm"
include "wa.mm"
include "wex.mm"
include "19.8a.mm"
include "nfv.mm"
include "sb8e.mm"
include "sylib.mm"
include "pm4.71i.mm"
include "19.42v.mm"
include "bitr4i.mm"
include "exbii.mm"

theorem pm11.58
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( E. x ph <-> E. x E. y ( ph /\ [ y / x ] ph ) )

  proof
    wph
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    vy
    wex
    #
    vx
    wph
    wph
    @0
    vy
    wex
    #
    wa
    @1
    wph
    @2
    wph
    wph
    vx
    wex
    @2
    wph
    vx
    19.8a
    wph
    vx
    vy
    wph
    vy
    nfv
    sb8e
    sylib
    pm4.71i
    wph
    @0
    vy
    19.42v
    bitr4i
    exbii
end
