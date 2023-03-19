include "wi.mm"
include "tb-ax2.mm"
include "tb-ax1.mm"
include "tbsyl.mm"
include "tb-ax3.mm"
include "mpsyl.mm"

theorem re1ax2lem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wps
    wps
    wch
    wi
    #
    wch
    wi
    #
    wi
    wph
    @0
    wi
    @1
    wph
    wch
    wi
    #
    wi
    wps
    @2
    wi
    wps
    @0
    @1
    wi
    #
    @1
    wps
    @0
    wps
    wi
    @3
    wps
    @0
    tb-ax2
    @0
    wps
    wch
    tb-ax1
    tbsyl
    @3
    @1
    wch
    wi
    @1
    wi
    @1
    @0
    @1
    wch
    tb-ax1
    @1
    wch
    tb-ax3
    tbsyl
    tbsyl
    wph
    @0
    wch
    tb-ax1
    wps
    @1
    @2
    tb-ax1
    mpsyl
end
