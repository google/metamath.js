include "weq.mm"
include "wal.mm"
include "wn.mm"
include "id.mm"
include "wl-naev.mm"
include "wl-2sb6d.mm"

theorem wl-sbcom2d-lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u v
  disjoint u x
  disjoint v x
  disjoint u y
  disjoint v y
  disjoint ph u
  disjoint ph v
  assert |- ( -. A. y y = x -> ( [ u / x ] [ v / y ] ph <-> A. x A. y ( ( x = u /\ y = v ) -> ph ) ) )

  proof
    vy
    vx
    weq
    vy
    wal
    wn
    #
    wph
    vx
    vy
    vu
    vv
    @0
    id
    vy
    vx
    vv
    vy
    wl-naev
    vy
    vx
    vu
    vy
    wl-naev
    vy
    vx
    vu
    vx
    wl-naev
    wl-2sb6d
end
