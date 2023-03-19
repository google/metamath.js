include "wvhc2.mm"
include "wvd1.mm"
include "wi.mm"
include "wa.mm"
include "df-vd1.mm"
include "df-vhc2.mm"
include "imbi1i.mm"
include "bitri.mm"

theorem dfvd2an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( (. (. ph ,. ps ). ->. ch ). <-> ( ( ph /\ ps ) -> ch ) )

  proof
    wph
    wps
    wvhc2
    #
    wch
    wvd1
    @0
    wch
    wi
    wph
    wps
    wa
    #
    wch
    wi
    @0
    wch
    df-vd1
    @0
    @1
    wch
    wph
    wps
    df-vhc2
    imbi1i
    bitri
end
