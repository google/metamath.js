include "wo.mm"
include "wi.mm"
include "wb.mm"
include "wn.mm"
include "ax-1.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "a1d.mm"
include "ja.mm"
include "ax-2.mm"
include "com3r.mm"
include "impbid2.mm"
include "2thd.mm"
include "jaoi.mm"
include "jarl.mm"
include "orrd.mm"
include "simplim.mm"
include "orcd.mm"
include "a1i.mm"
include "bija.mm"
include "impbii.mm"

theorem rp-fakeimass
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ch ) <-> ( ( ( ph -> ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) )

  proof
    wph
    wch
    wo
    #
    wph
    wps
    wi
    #
    wch
    wi
    #
    wph
    wps
    wch
    wi
    #
    wi
    #
    wb
    #
    wph
    @5
    wch
    wph
    @2
    @4
    @1
    wch
    @4
    @1
    wn
    #
    @3
    wph
    @6
    wps
    wch
    wps
    @1
    wps
    wph
    ax-1
    con3i
    pm2.21d
    a1d
    wch
    @3
    wph
    wch
    wps
    ax-1
    a1d
    #
    ja
    @4
    @1
    wph
    wch
    wph
    wps
    wch
    ax-2
    com3r
    impbid2
    wch
    @2
    @4
    wch
    @1
    ax-1
    @7
    2thd
    jaoi
    @2
    @4
    @0
    @2
    @0
    @4
    @2
    wph
    wch
    wph
    wps
    wch
    jarl
    orrd
    a1d
    @4
    wn
    #
    @0
    wi
    @2
    wn
    @8
    wph
    wch
    wph
    @3
    simplim
    orcd
    a1i
    bija
    impbii
end
