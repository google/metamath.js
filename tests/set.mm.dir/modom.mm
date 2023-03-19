include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "cab.mm"
include "c1o.mm"
include "cdom.mm"
include "wbr.mm"
include "df-mo.mm"
include "imor.mm"
include "csdm.mm"
include "cen.mm"
include "c0.mm"
include "wceq.mm"
include "abn0.mm"
include "necon1bbii.mm"
include "sdom1.mm"
include "bitr4i.mm"
include "euen1.mm"
include "orbi12i.mm"
include "brdom2.mm"
include "3bitri.mm"

theorem modom
  let wph: wff ph
  let vx: setvar x


  assert |- ( E* x ph <-> { x | ph } ~<_ 1o )

  proof
    wph
    vx
    wmo
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wi
    @0
    wn
    #
    @1
    wo
    #
    wph
    vx
    cab
    #
    c1o
    cdom
    wbr
    #
    wph
    vx
    df-mo
    @0
    @1
    imor
    @3
    @4
    c1o
    csdm
    wbr
    #
    @4
    c1o
    cen
    wbr
    #
    wo
    @5
    @2
    @6
    @1
    @7
    @2
    @4
    c0
    wceq
    @6
    @0
    @4
    c0
    wph
    vx
    abn0
    necon1bbii
    @4
    sdom1
    bitr4i
    wph
    vx
    euen1
    orbi12i
    @4
    c1o
    brdom2
    bitr4i
    3bitri
end
