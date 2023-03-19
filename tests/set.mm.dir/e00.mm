include "mp2.mm"

theorem e00
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume e00.1: |- ph
  assume e00.2: |- ps
  assume e00.3: |- ( ph -> ( ps -> ch ) )


  assert |- ch

  proof
    wph
    wps
    wch
    e00.1
    e00.2
    e00.3
    mp2
end
