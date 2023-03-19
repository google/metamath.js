include "wnf.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "19.38a.mm"
include "19.9t.mm"
include "imbi1d.mm"
include "bitr3d.mm"

theorem 19.21t
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) )

  proof
    wph
    vx
    wnf
    #
    wph
    vx
    wex
    #
    wps
    vx
    wal
    #
    wi
    wph
    wps
    wi
    vx
    wal
    wph
    @2
    wi
    wph
    wps
    vx
    19.38a
    @0
    @1
    wph
    @2
    wph
    vx
    19.9t
    imbi1d
    bitr3d
end
