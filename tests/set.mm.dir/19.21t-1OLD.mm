include "wnfOLD.mm"
include "wal.mm"
include "wi.mm"
include "nfrOLD.mm"
include "alim.mm"
include "syl9.mm"

theorem 19.21t-1OLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( nfOLD x ph -> ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnfOLD
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
    nfrOLD
    wph
    wps
    vx
    alim
    syl9
end
