include "wi.mm"
include "w3a.mm"
include "exp31.mm"
include "3expd.mm"

theorem exp516
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume exp516.1: |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wi
    wph
    wps
    wch
    wth
    w3a
    wta
    wet
    exp516.1
    exp31
    3expd
end
