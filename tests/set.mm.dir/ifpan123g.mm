include "wif.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "dfifp4.mm"
include "anbi12i.mm"

theorem ifpan123g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( if- ( ph , ch , ta ) /\ if- ( ps , th , et ) ) <-> ( ( ( -. ph \/ ch ) /\ ( ph \/ ta ) ) /\ ( ( -. ps \/ th ) /\ ( ps \/ et ) ) ) )

  proof
    wph
    wch
    wta
    wif
    wph
    wn
    wch
    wo
    wph
    wta
    wo
    wa
    wps
    wth
    wet
    wif
    wps
    wn
    wth
    wo
    wps
    wet
    wo
    wa
    wph
    wch
    wta
    dfifp4
    wps
    wth
    wet
    dfifp4
    anbi12i
end
