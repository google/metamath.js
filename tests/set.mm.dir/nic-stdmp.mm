include "wi.mm"
include "wnan.mm"
include "nic-dfim.mm"
include "nic-bi2.mm"
include "nic-mp.mm"

theorem nic-stdmp
  let wph: wff ph
  let wps: wff ps
  assume nic-smin: |- ph
  assume nic-smaj: |- ( ph -> ps )


  assert |- ps

  proof
    wph
    wps
    wps
    nic-smin
    wph
    wps
    wi
    #
    wph
    wps
    wps
    wnan
    wnan
    #
    @1
    nic-smaj
    @1
    @0
    wph
    wps
    nic-dfim
    nic-bi2
    nic-mp
    nic-mp
end
