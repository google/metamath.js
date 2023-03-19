include "wn.mm"
include "wi.mm"
include "wnan.mm"
include "nic-dfim.mm"
include "nic-bi2.mm"
include "nic-dfneg.mm"
include "nic-id.mm"
include "nic-iimp1.mm"
include "nic-isw2.mm"
include "nic-isw1.mm"
include "nic-bi1.mm"
include "nic-mp.mm"

theorem nic-luk2
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wn
    #
    wph
    wi
    #
    wph
    wph
    wnan
    #
    wnan
    #
    @1
    wph
    wi
    #
    @4
    @1
    @2
    @1
    @0
    @2
    wnan
    #
    @5
    @2
    @5
    @1
    @0
    wph
    nic-dfim
    nic-bi2
    @0
    @2
    @2
    @2
    @0
    wnan
    @0
    @0
    wnan
    @2
    @2
    wnan
    @2
    wph
    nic-dfneg
    @2
    nic-id
    nic-iimp1
    nic-isw2
    nic-iimp1
    nic-isw1
    @3
    @4
    @1
    wph
    nic-dfim
    nic-bi1
    nic-mp
end
