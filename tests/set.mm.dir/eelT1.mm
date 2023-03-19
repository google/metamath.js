include "trud.mm"
include "sylancr.mm"

theorem eelT1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume eelT1.1: |- ( T. -> ph )
  assume eelT1.2: |- ( ps -> ch )
  assume eelT1.3: |- ( ( ph /\ ch ) -> th )


  assert |- ( ps -> th )

  proof
    wps
    wph
    wch
    wth
    wph
    eelT1.1
    trud
    eelT1.2
    eelT1.3
    sylancr
end
