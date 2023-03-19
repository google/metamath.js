include "wa.mm"
include "biimpi.mm"
include "simpld.mm"

theorem simplbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume simplbi.1: |- ( ph <-> ( ps /\ ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    wa
    simplbi.1
    biimpi
    simpld
end
