include "ax-mp.mm"
include "mp2.mm"

theorem bj-mp2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bj-mp2d.1: |- ph
  assume bj-mp2d.2: |- ( ph -> ps )
  assume bj-mp2d.3: |- ( ps -> ( ph -> ch ) )


  assert |- ch

  proof
    wps
    wph
    wch
    wph
    wps
    bj-mp2d.1
    bj-mp2d.2
    ax-mp
    bj-mp2d.1
    bj-mp2d.3
    mp2
end
