include "wa.mm"
include "w3a.mm"
include "wi.mm"
include "pm3.2.mm"
include "ex.mm"
include "df-3an.mm"
include "bicomi.mm"
include "syl8ib.mm"

theorem pm3.2an3OLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) )

  proof
    wph
    wps
    wch
    wph
    wps
    wa
    #
    wch
    wa
    #
    wph
    wps
    wch
    w3a
    #
    wph
    wps
    wch
    @1
    wi
    @0
    wch
    pm3.2
    ex
    @2
    @1
    wph
    wps
    wch
    df-3an
    bicomi
    syl8ib
end
