include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "bj-nfdt0.mm"
include "imim2d.mm"

theorem bj-nfdt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> A. x ps ) ) -> ( ( ph -> A. x ph ) -> ( ph -> F/ x ps ) ) )

  proof
    wph
    wps
    wps
    vx
    wal
    wi
    wi
    vx
    wal
    wph
    vx
    wal
    wps
    vx
    wnf
    wph
    wph
    wps
    vx
    bj-nfdt0
    imim2d
end
