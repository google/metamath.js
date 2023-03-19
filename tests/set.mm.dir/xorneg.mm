include "wn.mm"
include "wxo.mm"
include "xorneg1.mm"
include "xorneg2.mm"
include "con2bii.mm"
include "bitr4i.mm"

theorem xorneg
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph \/_ -. ps ) <-> ( ph \/_ ps ) )

  proof
    wph
    wn
    wps
    wn
    #
    wxo
    wph
    @0
    wxo
    #
    wn
    wph
    wps
    wxo
    #
    wph
    @0
    xorneg1
    @1
    @2
    wph
    wps
    xorneg2
    con2bii
    bitr4i
end
