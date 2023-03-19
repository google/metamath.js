include "wi.mm"
include "wn.mm"
include "wa.mm"
include "notnotb.mm"
include "imbi2i.mm"
include "imnan.mm"
include "bitri.mm"

theorem iman
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> -. ( ph /\ -. ps ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wn
    #
    wn
    #
    wi
    wph
    @0
    wa
    wn
    wps
    @1
    wph
    wps
    notnotb
    imbi2i
    wph
    @0
    imnan
    bitri
end
