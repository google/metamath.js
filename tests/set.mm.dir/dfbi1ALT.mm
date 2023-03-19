include "wb.mm"
include "wi.mm"
include "wn.mm"
include "df-bi.mm"
include "ax-1.mm"
include "ax-mp.mm"
include "ax-3.mm"
include "ax-2.mm"

theorem dfbi1ALT
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wi
    wps
    wph
    wi
    wn
    wi
    wn
    #
    wi
    @1
    @0
    wi
    wn
    wi
    wn
    #
    @0
    @1
    wb
    #
    wph
    wps
    df-bi
    wch
    wth
    wch
    wi
    wi
    #
    @2
    @3
    wi
    #
    wch
    wth
    ax-1
    @5
    wn
    #
    @4
    wn
    #
    wi
    #
    @4
    @5
    wi
    @6
    @3
    @2
    wi
    #
    @6
    wi
    #
    wi
    #
    @8
    @6
    @9
    ax-1
    @6
    @10
    @7
    wi
    #
    wi
    #
    @11
    @8
    wi
    @12
    @13
    @7
    wn
    #
    @10
    wn
    #
    wi
    #
    @12
    @15
    @16
    @0
    @1
    df-bi
    @15
    @14
    ax-1
    ax-mp
    @7
    @10
    ax-3
    ax-mp
    @12
    @6
    ax-1
    ax-mp
    @6
    @10
    @7
    ax-2
    ax-mp
    ax-mp
    @5
    @4
    ax-3
    ax-mp
    ax-mp
    ax-mp
end
