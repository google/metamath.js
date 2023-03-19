include "ex.mm"
include "impbid.mm"

theorem impbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume impbida.1: |- ( ( ph /\ ps ) -> ch )
  assume impbida.2: |- ( ( ph /\ ch ) -> ps )


  assert |- ( ph -> ( ps <-> ch ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    impbida.1
    ex
    wph
    wch
    wps
    impbida.2
    ex
    impbid
end
