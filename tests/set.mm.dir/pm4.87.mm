include "wa.mm"
include "wi.mm"
include "wb.mm"
include "impexp.mm"
include "bi2.04.mm"
include "pm3.2i.mm"
include "bicomi.mm"

theorem pm4.87
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) /\ ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ) ) /\ ( ( ps -> ( ph -> ch ) ) <-> ( ( ps /\ ph ) -> ch ) ) )

  proof
    wph
    wps
    wa
    wch
    wi
    wph
    wps
    wch
    wi
    wi
    #
    wb
    #
    @0
    wps
    wph
    wch
    wi
    wi
    #
    wb
    #
    wa
    @2
    wps
    wph
    wa
    wch
    wi
    #
    wb
    @1
    @3
    wph
    wps
    wch
    impexp
    wph
    wps
    wch
    bi2.04
    pm3.2i
    @4
    @2
    wps
    wph
    wch
    impexp
    bicomi
    pm3.2i
end
