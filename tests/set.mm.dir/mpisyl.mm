include "mpi.mm"
include "syl.mm"

theorem mpisyl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume mpisyl.1: |- ( ph -> ps )
  assume mpisyl.2: |- ch
  assume mpisyl.3: |- ( ps -> ( ch -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wth
    mpisyl.1
    wps
    wch
    wth
    mpisyl.2
    mpisyl.3
    mpi
    syl
end
