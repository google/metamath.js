include "wi.mm"
include "wnan.mm"
include "nic-dfim.mm"
include "nic-bi2.mm"
include "nic-ax.mm"
include "nic-isw2.mm"
include "nic-idel.mm"
include "nic-bi1.mm"
include "nic-idbl.mm"
include "nic-imp.mm"
include "nic-swap.mm"
include "nic-ich.mm"
include "nic-mp.mm"

theorem nic-luk1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wi
    #
    wps
    wch
    wi
    #
    wph
    wch
    wi
    #
    wi
    #
    @3
    wnan
    wnan
    #
    @0
    @3
    wi
    #
    @5
    @0
    wph
    wps
    wps
    wnan
    wnan
    #
    @3
    @6
    @0
    wph
    wps
    nic-dfim
    nic-bi2
    @6
    @1
    @2
    @2
    wnan
    #
    wnan
    #
    @3
    @6
    wch
    wch
    wnan
    #
    wps
    wnan
    #
    wph
    @9
    wnan
    #
    @11
    wnan
    #
    wnan
    #
    @8
    @6
    wta
    wta
    wta
    wnan
    wnan
    #
    @13
    @13
    @6
    @14
    wph
    wps
    wps
    @9
    wta
    nic-ax
    nic-isw2
    nic-idel
    @13
    @7
    @10
    wnan
    @8
    @7
    @12
    @12
    @10
    @11
    @2
    @11
    @2
    wph
    wch
    nic-dfim
    nic-bi1
    nic-idbl
    nic-imp
    @1
    @10
    @10
    @7
    @1
    wps
    @9
    wnan
    #
    @10
    @15
    @1
    wps
    wch
    nic-dfim
    nic-bi2
    @9
    wps
    nic-swap
    nic-ich
    nic-imp
    nic-ich
    nic-ich
    @8
    @3
    @1
    @2
    nic-dfim
    nic-bi1
    nic-ich
    nic-ich
    @4
    @5
    @0
    @3
    nic-dfim
    nic-bi1
    nic-mp
end
