include "expd.mm"
include "mpid.mm"

theorem mpan2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpan2d.1: |- ( ph -> ch )
  assume mpan2d.2: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    mpan2d.1
    wph
    wps
    wch
    wth
    mpan2d.2
    expd
    mpid
end
