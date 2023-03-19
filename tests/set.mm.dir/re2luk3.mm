include "wn.mm"
include "wi.mm"
include "wo.mm"
include "rb-imdf.mm"
include "rblem7.mm"
include "rb-ax4.mm"
include "rb-ax3.mm"
include "rbsyl.mm"
include "rb-ax2.mm"
include "anmp.mm"
include "rblem2.mm"

theorem re2luk3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( -. ph -> ps ) )

  proof
    wph
    wn
    #
    @0
    wps
    wi
    #
    wo
    #
    wph
    @1
    wi
    #
    @0
    @0
    wn
    #
    wps
    wo
    #
    @1
    @1
    @5
    @0
    wps
    rb-imdf
    rblem7
    @0
    @4
    wo
    #
    @0
    @5
    wo
    @4
    @0
    wo
    @6
    @4
    @0
    @0
    wo
    @0
    @0
    rb-ax4
    @0
    @0
    rb-ax3
    rbsyl
    @4
    @0
    rb-ax2
    anmp
    @4
    wps
    @0
    rblem2
    anmp
    rbsyl
    @3
    @2
    wph
    @1
    rb-imdf
    rblem7
    anmp
end
