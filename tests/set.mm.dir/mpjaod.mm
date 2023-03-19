include "wo.mm"
include "jaod.mm"
include "mpd.mm"

theorem mpjaod
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume jaod.1: |- ( ph -> ( ps -> ch ) )
  assume jaod.2: |- ( ph -> ( th -> ch ) )
  assume jaod.3: |- ( ph -> ( ps \/ th ) )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wth
    wo
    wch
    jaod.3
    wph
    wps
    wch
    wth
    jaod.1
    jaod.2
    jaod
    mpd
end
