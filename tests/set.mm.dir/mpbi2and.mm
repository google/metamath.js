include "wa.mm"
include "jca.mm"
include "mpbid.mm"

theorem mpbi2and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpbi2and.1: |- ( ph -> ps )
  assume mpbi2and.2: |- ( ph -> ch )
  assume mpbi2and.3: |- ( ph -> ( ( ps /\ ch ) <-> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wa
    wth
    wph
    wps
    wch
    mpbi2and.1
    mpbi2and.2
    jca
    mpbi2and.3
    mpbid
end
