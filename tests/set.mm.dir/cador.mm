include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wcad.mm"
include "w3o.mm"
include "wn.mm"
include "wi.mm"
include "xor2.mm"
include "rbaib.mm"
include "anbi1d.mm"
include "ancom.mm"
include "andir.mm"
include "3bitr3g.mm"
include "pm5.74i.mm"
include "df-or.mm"
include "3bitr4i.mm"
include "df-cad.mm"
include "3orass.mm"

theorem cador
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) )

  proof
    wph
    wps
    wa
    #
    wch
    wph
    wps
    wxo
    #
    wa
    #
    wo
    #
    @0
    wph
    wch
    wa
    #
    wps
    wch
    wa
    #
    wo
    #
    wo
    #
    wph
    wps
    wch
    wcad
    @0
    @4
    @5
    w3o
    @0
    wn
    #
    @2
    wi
    @8
    @6
    wi
    @3
    @7
    @8
    @2
    @6
    @8
    @1
    wch
    wa
    wph
    wps
    wo
    #
    wch
    wa
    @2
    @6
    @8
    @1
    @9
    wch
    @1
    @9
    @8
    wph
    wps
    xor2
    rbaib
    anbi1d
    @1
    wch
    ancom
    wph
    wps
    wch
    andir
    3bitr3g
    pm5.74i
    @0
    @2
    df-or
    @0
    @6
    df-or
    3bitr4i
    wph
    wps
    wch
    df-cad
    @0
    @4
    @5
    3orass
    3bitr4i
end
