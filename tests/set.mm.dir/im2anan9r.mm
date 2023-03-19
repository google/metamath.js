include "wa.mm"
include "wi.mm"
include "im2anan9.mm"
include "ancoms.mm"

theorem im2anan9r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume im2an9.1: |- ( ph -> ( ps -> ch ) )
  assume im2an9.2: |- ( th -> ( ta -> et ) )


  assert |- ( ( th /\ ph ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) )

  proof
    wph
    wth
    wps
    wta
    wa
    wch
    wet
    wa
    wi
    wph
    wps
    wch
    wth
    wta
    wet
    im2an9.1
    im2an9.2
    im2anan9
    ancoms
end
