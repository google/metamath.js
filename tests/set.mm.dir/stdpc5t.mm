include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "nf5r.mm"
include "alim.mm"
include "syl9.mm"

theorem stdpc5t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnf
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
    nf5r
    wph
    wps
    vx
    alim
    syl9
end
