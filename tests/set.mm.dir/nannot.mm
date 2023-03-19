include "wnan.mm"
include "wn.mm"
include "wa.mm"
include "df-nan.mm"
include "anidm.mm"
include "xchbinx.mm"
include "bicomi.mm"

theorem nannot
  let wps: wff ps


  assert |- ( -. ps <-> ( ps -/\ ps ) )

  proof
    wps
    wps
    wnan
    #
    wps
    wn
    @0
    wps
    wps
    wa
    wps
    wps
    wps
    df-nan
    wps
    anidm
    xchbinx
    bicomi
end
