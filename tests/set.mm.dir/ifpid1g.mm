include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "ifpidg.mm"
include "ancom.mm"
include "pm4.25.mm"
include "imbi2i.mm"
include "orc.mm"
include "biantru.mm"
include "bitr2i.mm"
include "pm4.24.mm"
include "imbi1i.mm"
include "simpl.mm"
include "biantrur.mm"
include "anbi12i.mm"
include "3bitri.mm"

theorem ifpid1g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> if- ( ph , ps , ch ) ) <-> ( ( ch -> ph ) /\ ( ph -> ps ) ) )

  proof
    wph
    wph
    wps
    wch
    wif
    wb
    wph
    wps
    wa
    wph
    wi
    #
    wph
    wph
    wa
    #
    wps
    wi
    #
    wa
    #
    wch
    wph
    wph
    wo
    #
    wi
    #
    wph
    wph
    wch
    wo
    wi
    #
    wa
    #
    wa
    @7
    @3
    wa
    wch
    wph
    wi
    #
    wph
    wps
    wi
    #
    wa
    wph
    wps
    wch
    wph
    ifpidg
    @3
    @7
    ancom
    @7
    @8
    @3
    @9
    @8
    @5
    @7
    wph
    @4
    wch
    wph
    pm4.25
    imbi2i
    @6
    @5
    wph
    wch
    orc
    biantru
    bitr2i
    @9
    @2
    @3
    wph
    @1
    wps
    wph
    pm4.24
    imbi1i
    @0
    @2
    wph
    wps
    simpl
    biantrur
    bitr2i
    anbi12i
    3bitri
end
