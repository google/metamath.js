include "wal.mm"
include "wi.mm"
include "ax-5.mm"
include "alim.mm"
include "syl5.mm"

theorem stdpc5v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) )

  proof
    wph
    wph
    vx
    wal
    wph
    wps
    wi
    vx
    wal
    wps
    vx
    wal
    wph
    vx
    ax-5
    wph
    wps
    vx
    alim
    syl5
end
