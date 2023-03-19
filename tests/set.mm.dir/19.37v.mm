include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "19.3v.mm"
include "imbi1i.mm"
include "bitri.mm"

theorem 19.37v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) )

  proof
    wph
    wps
    wi
    vx
    wex
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wi
    wph
    @1
    wi
    wph
    wps
    vx
    19.35
    @0
    wph
    @1
    wph
    vx
    19.3v
    imbi1i
    bitri
end
