include "wtru.mm"
include "sylan.mm"
include "mpan2.mm"
include "trud.mm"

theorem eelT0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume eelT0.1: |- ( T. -> ph )
  assume eelT0.2: |- ps
  assume eelT0.3: |- ( ( ph /\ ps ) -> ch )


  assert |- ch

  proof
    wch
    wtru
    wps
    wch
    eelT0.2
    wtru
    wph
    wps
    wch
    eelT0.1
    eelT0.3
    sylan
    mpan2
    trud
end
