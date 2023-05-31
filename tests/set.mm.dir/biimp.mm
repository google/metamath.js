include "wb.mm"
include "wi.mm"
include "wn.mm"
include "df-bi.mm"
include "simplim.mm"
include "ax-mp.mm"
include "syl.mm"

theorem biimp
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ph -> ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wi
    #
    wps
    wph
    wi
    wn
    #
    wi
    wn
    #
    @1
    @0
    @3
    wi
    #
    @3
    @0
    wi
    wn
    #
    wi
    wn
    @4
    wph
    wps
    df-bi
    @4
    @5
    simplim
    ax-mp
    @1
    @2
    simplim
    syl
end
