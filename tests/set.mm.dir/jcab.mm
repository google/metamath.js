include "wa.mm"
include "wi.mm"
include "simpl.mm"
include "imim2i.mm"
include "simpr.mm"
include "jca.mm"
include "pm3.43.mm"
include "impbii.mm"

theorem jcab
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps /\ ch ) ) <-> ( ( ph -> ps ) /\ ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wi
    #
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wa
    @1
    @2
    @3
    @0
    wps
    wph
    wps
    wch
    simpl
    imim2i
    @0
    wch
    wph
    wps
    wch
    simpr
    imim2i
    jca
    wph
    wps
    wch
    pm3.43
    impbii
end
