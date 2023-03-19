include "wa.mm"
include "wi.mm"
include "adantr.mm"
include "adantl.mm"
include "anim12d.mm"

theorem im2anan9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume im2an9.1: |- ( ph -> ( ps -> ch ) )
  assume im2an9.2: |- ( th -> ( ta -> et ) )


  assert |- ( ( ph /\ th ) -> ( ( ps /\ ta ) -> ( ch /\ et ) ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wta
    wet
    wph
    wps
    wch
    wi
    wth
    im2an9.1
    adantr
    wth
    wta
    wet
    wi
    wph
    im2an9.2
    adantl
    anim12d
end
