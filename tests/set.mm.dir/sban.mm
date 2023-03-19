include "wn.mm"
include "wi.mm"
include "wsb.mm"
include "wa.mm"
include "sbn.mm"
include "sbim.mm"
include "imbi2i.mm"
include "bitri.mm"
include "xchbinx.mm"
include "df-an.mm"
include "sbbii.mm"
include "3bitr4i.mm"

theorem sban
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) )

  proof
    wph
    wps
    wn
    #
    wi
    #
    wn
    #
    vx
    vy
    wsb
    #
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wn
    #
    wi
    #
    wn
    wph
    wps
    wa
    #
    vx
    vy
    wsb
    @4
    @5
    wa
    @3
    @1
    vx
    vy
    wsb
    #
    @7
    @1
    vx
    vy
    sbn
    @9
    @4
    @0
    vx
    vy
    wsb
    #
    wi
    @7
    wph
    @0
    vx
    vy
    sbim
    @10
    @6
    @4
    wps
    vx
    vy
    sbn
    imbi2i
    bitri
    xchbinx
    @8
    @2
    vx
    vy
    wph
    wps
    df-an
    sbbii
    @4
    @5
    df-an
    3bitr4i
end
