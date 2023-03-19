include "a1i.mm"
include "mpan2d.mm"

theorem mpan2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpan2i.1: |- ch
  assume mpan2i.2: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    wch
    wph
    mpan2i.1
    a1i
    mpan2i.2
    mpan2d
end
