include "wex.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem bnj133
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj133.1: |- ( ph <-> E. x ps )
  assume bnj133.2: |- ( ch <-> ps )


  assert |- ( ph <-> E. x ch )

  proof
    wph
    wps
    vx
    wex
    wch
    vx
    wex
    bnj133.1
    wch
    wps
    vx
    bnj133.2
    exbii
    bitr4i
end
