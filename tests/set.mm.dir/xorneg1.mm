include "wn.mm"
include "wxo.mm"
include "xorcom.mm"
include "xorneg2.mm"
include "xchbinx.mm"
include "bitri.mm"

theorem xorneg1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph \/_ ps ) <-> -. ( ph \/_ ps ) )

  proof
    wph
    wn
    #
    wps
    wxo
    wps
    @0
    wxo
    #
    wph
    wps
    wxo
    #
    wn
    @0
    wps
    xorcom
    @1
    wps
    wph
    wxo
    @2
    wps
    wph
    xorneg2
    wps
    wph
    xorcom
    xchbinx
    bitri
end
