include "wi.mm"
include "wo.mm"
include "wa.mm"
include "wb.mm"
include "wn.mm"
include "pm1.4.mm"
include "ord.mm"
include "pm4.83.mm"
include "biimpi.mm"
include "sylan2.mm"
include "ex.mm"
include "anim1d.mm"
include "orc.mm"
include "anim1i.mm"
include "jctir.mm"
include "olc.mm"
include "jca.mm"
include "simpl.mm"
include "imim12i.mm"
include "adantr.mm"
include "impbii.mm"
include "dfbi2.mm"
include "ordir.mm"
include "bicomi.mm"
include "bibi1i.mm"
include "3bitr2i.mm"

theorem rp-fakeanorass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ch -> ph ) <-> ( ( ( ph /\ ps ) \/ ch ) <-> ( ph /\ ( ps \/ ch ) ) ) )

  proof
    wch
    wph
    wi
    #
    wph
    wch
    wo
    #
    wps
    wch
    wo
    #
    wa
    #
    wph
    @2
    wa
    #
    wi
    #
    @4
    @3
    wi
    #
    wa
    #
    @3
    @4
    wb
    wph
    wps
    wa
    wch
    wo
    #
    @4
    wb
    @0
    @7
    @0
    @5
    @6
    @0
    @1
    wph
    @2
    @0
    @1
    wph
    @1
    @0
    wch
    wn
    wph
    wi
    #
    wph
    @1
    wch
    wph
    wph
    wch
    pm1.4
    ord
    @0
    @9
    wa
    wph
    wch
    wph
    pm4.83
    biimpi
    sylan2
    ex
    anim1d
    wph
    @1
    @2
    wph
    wch
    orc
    anim1i
    jctir
    @5
    @0
    @6
    wch
    @3
    @4
    wph
    wch
    @1
    @2
    wch
    wph
    olc
    wch
    wps
    olc
    jca
    wph
    @2
    simpl
    imim12i
    adantr
    impbii
    @3
    @4
    dfbi2
    @3
    @8
    @4
    @8
    @3
    wph
    wps
    wch
    ordir
    bicomi
    bibi1i
    3bitr2i
end
