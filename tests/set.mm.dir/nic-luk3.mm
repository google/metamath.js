include "wn.mm"
include "wi.mm"
include "wnan.mm"
include "nic-dfim.mm"
include "nic-bi1.mm"
include "nic-dfneg.mm"
include "nic-bi2.mm"
include "nic-id.mm"
include "nic-iimp1.mm"
include "nic-iimp2.mm"
include "nic-mp.mm"

theorem nic-luk3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wph
    wn
    #
    wps
    wi
    #
    @1
    wnan
    wnan
    #
    wph
    @1
    wi
    #
    @3
    @0
    wps
    wps
    wnan
    #
    @1
    wph
    @0
    @4
    wnan
    @1
    @0
    wps
    nic-dfim
    nic-bi1
    @0
    wph
    wph
    wnan
    #
    @5
    wph
    @5
    @0
    wph
    nic-dfneg
    nic-bi2
    wph
    nic-id
    nic-iimp1
    nic-iimp2
    @2
    @3
    wph
    @1
    nic-dfim
    nic-bi1
    nic-mp
end
