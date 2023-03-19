include "mp2an.mm"

theorem e00an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume e00an.1: |- ph
  assume e00an.2: |- ps
  assume e00an.3: |- ( ( ph /\ ps ) -> ch )


  assert |- ch

  proof
    wph
    wps
    wch
    e00an.1
    e00an.2
    e00an.3
    mp2an
end
