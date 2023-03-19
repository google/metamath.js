include "wn.mm"
include "wi.mm"
include "wo.mm"
include "rb-ax4.mm"
include "rb-ax3.mm"
include "rbsyl.mm"
include "rb-ax2.mm"
include "anmp.mm"
include "rblem1.mm"
include "rb-imdf.mm"
include "rblem6.mm"
include "rblem7.mm"

theorem re2luk2
  let wph: wff ph


  assert |- ( ( -. ph -> ph ) -> ph )

  proof
    wph
    wn
    #
    wph
    wi
    #
    wn
    #
    wph
    wo
    #
    @1
    wph
    wi
    #
    @2
    @0
    wn
    #
    wph
    wo
    #
    wph
    @6
    wn
    wph
    wph
    wo
    #
    wph
    wph
    rb-ax4
    #
    @5
    wph
    wph
    wph
    @0
    wph
    wo
    @5
    wn
    #
    wph
    wo
    @0
    @7
    wph
    @8
    wph
    wph
    rb-ax3
    rbsyl
    #
    @0
    @9
    wph
    wph
    @9
    @5
    wo
    @5
    @9
    wo
    @9
    @5
    @5
    wo
    @5
    @5
    rb-ax4
    @5
    @5
    rb-ax3
    rbsyl
    @9
    @5
    rb-ax2
    anmp
    @10
    rblem1
    anmp
    @10
    rblem1
    rbsyl
    @1
    @6
    @0
    wph
    rb-imdf
    rblem6
    rbsyl
    @4
    @3
    @1
    wph
    rb-imdf
    rblem7
    anmp
end
