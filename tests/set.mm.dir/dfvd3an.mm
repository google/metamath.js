include "wvhc3.mm"
include "wvd1.mm"
include "wi.mm"
include "w3a.mm"
include "df-vd1.mm"
include "df-vhc3.mm"
include "imbi1i.mm"
include "bitri.mm"

theorem dfvd3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( (. (. ph ,. ps ,. ch ). ->. th ). <-> ( ( ph /\ ps /\ ch ) -> th ) )

  proof
    wph
    wps
    wch
    wvhc3
    #
    wth
    wvd1
    @0
    wth
    wi
    wph
    wps
    wch
    w3a
    #
    wth
    wi
    @0
    wth
    df-vd1
    @0
    @1
    wth
    wph
    wps
    wch
    df-vhc3
    imbi1i
    bitri
end
