include "ax-mp.mm"

theorem mp2b
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume mp2b.1: |- ph
  assume mp2b.2: |- ( ph -> ps )
  assume mp2b.3: |- ( ps -> ch )


  assert |- ch

  proof
    wps
    wch
    wph
    wps
    mp2b.1
    mp2b.2
    ax-mp
    mp2b.3
    ax-mp
end
