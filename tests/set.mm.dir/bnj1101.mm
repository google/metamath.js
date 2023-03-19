include "wi.mm"
include "wex.mm"
include "wa.mm"
include "pm3.42.mm"
include "bnj101.mm"
include "pm4.71i.mm"
include "imbi1i.mm"
include "exbii.mm"
include "mpbir.mm"

theorem bnj1101
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bnj1101.1: |- E. x ( ph -> ps )
  assume bnj1101.2: |- ( ch -> ph )


  assert |- E. x ( ch -> ps )

  proof
    wch
    wps
    wi
    #
    vx
    wex
    wch
    wph
    wa
    #
    wps
    wi
    #
    vx
    wex
    wph
    wps
    wi
    @2
    vx
    bnj1101.1
    wch
    wph
    wps
    pm3.42
    bnj101
    @0
    @2
    vx
    wch
    @1
    wps
    wch
    wph
    bnj1101.2
    pm4.71i
    imbi1i
    exbii
    mpbir
end
