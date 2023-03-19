include "wa.mm"
include "wi.mm"
include "wn.mm"
include "wnan.mm"
include "df-nan.mm"
include "anbi2i.mm"
include "xchbinx.mm"
include "mpbi.mm"
include "iman.mm"
include "mpbir.mm"
include "simprd.mm"
include "ax-mp.mm"

theorem nic-mpALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume nic-jmin: |- ph
  assume nic-jmaj: |- ( ph -/\ ( ch -/\ ps ) )


  assert |- ps

  proof
    wph
    wps
    nic-jmin
    wph
    wch
    wps
    wph
    wch
    wps
    wa
    #
    wi
    wph
    @0
    wn
    #
    wa
    #
    wn
    #
    wph
    wch
    wps
    wnan
    #
    wnan
    #
    @3
    nic-jmaj
    @5
    wph
    @4
    wa
    @2
    wph
    @4
    df-nan
    @4
    @1
    wph
    wch
    wps
    df-nan
    anbi2i
    xchbinx
    mpbi
    wph
    @0
    iman
    mpbir
    simprd
    ax-mp
end
