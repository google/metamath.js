include "wi.mm"
include "wn.mm"
include "wif.mm"
include "wb.mm"
include "wa.mm"
include "wo.mm"
include "ifpidg.mm"
include "dfor2.mm"
include "imbi2i.mm"
include "impexp.mm"
include "ax-1.mm"
include "adantl.mm"
include "biantrur.mm"
include "3bitr2i.mm"
include "imdi.mm"
include "imor.mm"
include "orcom.mm"
include "bitri.mm"
include "pm2.21.mm"
include "olcd.mm"
include "anbi12i.mm"
include "ancom.mm"

theorem ifpim23g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) <-> if- ( ch , ps , -. ph ) ) <-> ( ( ( ph /\ ps ) -> ch ) /\ ( ch -> ( ph \/ ps ) ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    wps
    wph
    wn
    #
    wif
    wb
    wch
    wps
    wa
    @0
    wi
    #
    wch
    @0
    wa
    wps
    wi
    #
    wa
    #
    @1
    wch
    @0
    wo
    wi
    #
    @0
    wch
    @1
    wo
    #
    wi
    #
    wa
    #
    wa
    wch
    wph
    wps
    wo
    #
    wi
    #
    wph
    wps
    wa
    wch
    wi
    #
    wa
    @11
    @10
    wa
    wch
    wps
    @1
    @0
    ifpidg
    @10
    @4
    @11
    @8
    @10
    wch
    @0
    wps
    wi
    #
    wi
    @3
    @4
    @9
    @12
    wch
    wph
    wps
    dfor2
    imbi2i
    wch
    @0
    wps
    impexp
    @2
    @3
    wps
    @0
    wch
    wps
    wph
    ax-1
    adantl
    biantrur
    3bitr2i
    @11
    @7
    @8
    @11
    wph
    wps
    wch
    wi
    wi
    #
    @7
    wph
    wps
    wch
    impexp
    @13
    @0
    wph
    wch
    wi
    #
    wi
    @7
    wph
    wps
    wch
    imdi
    @14
    @6
    @0
    @14
    @1
    wch
    wo
    @6
    wph
    wch
    imor
    @1
    wch
    orcom
    bitri
    imbi2i
    bitri
    bitri
    @5
    @7
    @1
    @0
    wch
    wph
    wps
    pm2.21
    olcd
    biantrur
    bitri
    anbi12i
    @10
    @11
    ancom
    3bitr2i
end
