include "wxo.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "xor2.mm"
include "df-or.mm"
include "imnan.mm"
include "bicomi.mm"
include "anbi12i.mm"
include "df-an.mm"
include "3bitri.mm"

theorem dfxor4
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> -. ( ( -. ph -> ps ) -> -. ( ph -> -. ps ) ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wo
    #
    wph
    wps
    wa
    wn
    #
    wa
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
    wa
    @2
    @3
    wn
    wi
    wn
    wph
    wps
    xor2
    @0
    @2
    @1
    @3
    wph
    wps
    df-or
    @3
    @1
    wph
    wps
    imnan
    bicomi
    anbi12i
    @2
    @3
    df-an
    3bitri
end
