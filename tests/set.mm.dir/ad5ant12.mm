include "wa.mm"
include "ad3antrrr.mm"

theorem ad5ant12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad5ant12.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ( ph /\ ps ) /\ th ) /\ ta ) /\ et ) -> ch )

  proof
    wph
    wps
    wa
    wch
    wth
    wta
    wet
    ad5ant12.1
    ad3antrrr
end
