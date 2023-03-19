include "wb.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3orbi123d.mm"

theorem 3orbi123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) ) -> ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ) )

  proof
    wph
    wps
    wb
    #
    wch
    wth
    wb
    #
    wta
    wet
    wb
    #
    w3a
    wph
    wps
    wch
    wth
    wta
    wet
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    3orbi123d
end
