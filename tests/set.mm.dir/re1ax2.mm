include "wi.mm"
include "re1ax2lem.mm"
include "tb-ax1.mm"
include "tb-ax3.mm"
include "tbsyl.mm"
include "ax-mp.mm"
include "mpsyl.mm"

theorem re1ax2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    wps
    wph
    wch
    wi
    #
    wi
    #
    wph
    wps
    wi
    #
    @0
    wi
    #
    wph
    wps
    wch
    re1ax2lem
    wph
    @0
    wi
    #
    @0
    wi
    #
    @1
    @2
    @4
    wi
    #
    @3
    @4
    @0
    wch
    wi
    @0
    wi
    @0
    wph
    @0
    wch
    tb-ax1
    @0
    wch
    tb-ax3
    tbsyl
    @2
    @1
    @4
    wi
    wi
    @1
    @6
    wi
    wph
    wps
    @0
    tb-ax1
    @2
    @1
    @4
    re1ax2lem
    ax-mp
    @6
    @5
    @3
    wi
    wi
    @5
    @6
    @3
    wi
    wi
    @2
    @4
    @0
    tb-ax1
    @6
    @5
    @3
    re1ax2lem
    ax-mp
    mpsyl
    tbsyl
end
