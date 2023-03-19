include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "ifpidg.mm"
include "simpr.mm"
include "pm3.2i.mm"
include "biantrur.mm"
include "ancom.mm"
include "3bitr2i.mm"

theorem ifpid2g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ps <-> if- ( ph , ps , ch ) ) <-> ( ( ps -> ( ph \/ ch ) ) /\ ( ch -> ( ph \/ ps ) ) ) )

  proof
    wps
    wph
    wps
    wch
    wif
    wb
    wph
    wps
    wa
    wps
    wi
    #
    @0
    wa
    #
    wch
    wph
    wps
    wo
    wi
    #
    wps
    wph
    wch
    wo
    wi
    #
    wa
    #
    wa
    @4
    @3
    @2
    wa
    wph
    wps
    wch
    wps
    ifpidg
    @1
    @4
    @0
    @0
    wph
    wps
    simpr
    #
    @5
    pm3.2i
    biantrur
    @2
    @3
    ancom
    3bitr2i
end
