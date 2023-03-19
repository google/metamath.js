include "ax-mp.mm"
include "mp2.mm"

theorem bj-mp2c
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume bj-mp2c.1: |- ph
  assume bj-mp2c.2: |- ( ph -> ps )
  assume bj-mp2c.3: |- ( ph -> ( ps -> ch ) )


  assert |- ch

  proof
    wph
    wps
    wch
    bj-mp2c.1
    wph
    wps
    bj-mp2c.1
    bj-mp2c.2
    ax-mp
    bj-mp2c.3
    mp2
end
