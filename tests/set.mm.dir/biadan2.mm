include "wa.mm"
include "pm4.71ri.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem biadan2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume biadan2.1: |- ( ph -> ps )
  assume biadan2.2: |- ( ps -> ( ph <-> ch ) )


  assert |- ( ph <-> ( ps /\ ch ) )

  proof
    wph
    wps
    wph
    wa
    wps
    wch
    wa
    wph
    wps
    biadan2.1
    pm4.71ri
    wps
    wph
    wch
    biadan2.2
    pm5.32i
    bitri
end
