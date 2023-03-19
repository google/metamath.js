include "wi.mm"
include "wo.mm"
include "olc.mm"
include "imim2i.mm"
include "jao.mm"
include "mpsyl.mm"
include "id.mm"
include "mp2.mm"
include "syl6com.mm"

theorem bj-currypeirce
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/ ( ph -> ps ) ) -> ( ( ( ph -> ps ) -> ph ) -> ph ) )

  proof
    wph
    wps
    wi
    #
    wph
    wi
    #
    wph
    @0
    wo
    #
    wph
    wph
    wo
    #
    wph
    wph
    @3
    wi
    @1
    @0
    @3
    wi
    @2
    @3
    wi
    wph
    wph
    olc
    #
    wph
    @3
    @0
    @4
    imim2i
    wph
    @3
    @0
    jao
    mpsyl
    wph
    wph
    wi
    #
    @5
    @3
    wph
    wi
    wph
    id
    #
    @6
    wph
    wph
    wph
    jao
    mp2
    syl6com
end
