include "a1i.mm"
include "sylc.mm"

theorem mpsyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpsyl.1: |- ph
  assume mpsyl.2: |- ( ps -> ch )
  assume mpsyl.3: |- ( ph -> ( ch -> th ) )


  assert |- ( ps -> th )

  proof
    wps
    wph
    wch
    wth
    wph
    wps
    mpsyl.1
    a1i
    mpsyl.2
    mpsyl.3
    sylc
end
