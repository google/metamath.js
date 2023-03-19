include "wal.mm"
include "weq.mm"
include "wi.mm"
include "ala1.mm"
include "a1i.mm"

theorem ax12dgen
  let wph: wff ph
  let vx: setvar x


  assert |- ( x = x -> ( A. x ph -> A. x ( x = x -> ph ) ) )

  proof
    wph
    vx
    wal
    vx
    vx
    weq
    #
    wph
    wi
    vx
    wal
    wi
    @0
    wph
    @0
    vx
    ala1
    a1i
end
