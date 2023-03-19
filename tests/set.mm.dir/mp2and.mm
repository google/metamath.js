include "mpand.mm"
include "mpd.mm"

theorem mp2and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mp2and.1: |- ( ph -> ps )
  assume mp2and.2: |- ( ph -> ch )
  assume mp2and.3: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wch
    wth
    mp2and.2
    wph
    wps
    wch
    wth
    mp2and.1
    mp2and.3
    mpand
    mpd
end
