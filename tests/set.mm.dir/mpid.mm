include "a1d.mm"
include "mpdd.mm"

theorem mpid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpid.1: |- ( ph -> ch )
  assume mpid.2: |- ( ph -> ( ps -> ( ch -> th ) ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wch
    wps
    mpid.1
    a1d
    mpid.2
    mpdd
end
