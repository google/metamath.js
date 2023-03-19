include "weq.mm"
include "wi.mm"
include "wal.mm"
include "ax12v2.mm"
include "ax-gen.mm"

theorem bj-ax12
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t

  disjoint t x
  assert |- A. x ( x = t -> ( ph -> A. x ( x = t -> ph ) ) )

  proof
    vx
    vt
    weq
    #
    wph
    @0
    wph
    wi
    vx
    wal
    wi
    wi
    vx
    wph
    vx
    vt
    ax12v2
    ax-gen
end
