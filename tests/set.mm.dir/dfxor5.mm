include "wxo.mm"
include "wn.mm"
include "wi.mm"
include "dfxor4.mm"
include "con2b.mm"
include "xchbinx.mm"

theorem dfxor5
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> -. ( ( ph -> -. ps ) -> -. ( -. ph -> ps ) ) )

  proof
    wph
    wps
    wxo
    wph
    wn
    wps
    wi
    #
    wph
    wps
    wn
    wi
    #
    wn
    wi
    @1
    @0
    wn
    wi
    wph
    wps
    dfxor4
    @0
    @1
    con2b
    xchbinx
end
