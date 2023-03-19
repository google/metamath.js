include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "biid.mm"
include "2uasbanh.mm"

theorem 2uasban
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( E. x E. y ( ( x = u /\ y = v ) /\ ( ph /\ ps ) ) <-> ( E. x E. y ( ( x = u /\ y = v ) /\ ph ) /\ E. x E. y ( ( x = u /\ y = v ) /\ ps ) ) )

  proof
    wph
    wps
    vx
    cv
    vu
    cv
    wceq
    vy
    cv
    vv
    cv
    wceq
    wa
    #
    wph
    wa
    vy
    wex
    vx
    wex
    @0
    wps
    wa
    vy
    wex
    vx
    wex
    wa
    #
    vx
    vy
    vv
    vu
    @1
    biid
    2uasbanh
end
