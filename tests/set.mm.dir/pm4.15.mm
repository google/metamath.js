include "wa.mm"
include "wn.mm"
include "wi.mm"
include "con2b.mm"
include "nan.mm"
include "bitr2i.mm"

theorem pm4.15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) -> -. ch ) <-> ( ( ps /\ ch ) -> -. ph ) )

  proof
    wps
    wch
    wa
    #
    wph
    wn
    wi
    wph
    @0
    wn
    wi
    wph
    wps
    wa
    wch
    wn
    wi
    @0
    wph
    con2b
    wph
    wps
    wch
    nan
    bitr2i
end
