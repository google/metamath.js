include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wb.mm"
include "exmid.mm"
include "biantrur.mm"
include "a1i.mm"
include "andir.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "syl5.mm"
include "pm5.32d.mm"
include "iffalse.mm"
include "orbi12d.mm"
include "3bitrd.mm"

theorem elimifd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
  assume elimifd.1: |- ( ph -> ( if ( ps , A , B ) = A -> ( ch <-> th ) ) )
  assume elimifd.2: |- ( ph -> ( if ( ps , A , B ) = B -> ( ch <-> ta ) ) )


  assert |- ( ph -> ( ch <-> ( ( ps /\ th ) \/ ( -. ps /\ ta ) ) ) )

  proof
    wph
    wch
    wps
    wps
    wn
    #
    wo
    #
    wch
    wa
    #
    wps
    wch
    wa
    #
    @0
    wch
    wa
    #
    wo
    #
    wps
    wth
    wa
    #
    @0
    wta
    wa
    #
    wo
    wch
    @2
    wb
    wph
    @1
    wch
    wps
    exmid
    biantrur
    a1i
    @2
    @5
    wb
    wph
    wps
    @0
    wch
    andir
    a1i
    wph
    @3
    @6
    @4
    @7
    wph
    wps
    wch
    wth
    wps
    wps
    cA
    cB
    cif
    #
    cA
    wceq
    wph
    wch
    wth
    wb
    wps
    cA
    cB
    iftrue
    elimifd.1
    syl5
    pm5.32d
    wph
    @0
    wch
    wta
    @0
    @8
    cB
    wceq
    wph
    wch
    wta
    wb
    wps
    cA
    cB
    iffalse
    elimifd.2
    syl5
    pm5.32d
    orbi12d
    3bitrd
end
