include "wi.mm"
include "wex.mm"
include "19.37v.mm"
include "bitri.mm"

theorem bnj132
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj132.1: |- ( ph <-> E. x ( ps -> ch ) )

  disjoint ps x
  assert |- ( ph <-> ( ps -> E. x ch ) )

  proof
    wph
    wps
    wch
    wi
    vx
    wex
    wps
    wch
    vx
    wex
    wi
    bnj132.1
    wps
    wch
    vx
    19.37v
    bitri
end
