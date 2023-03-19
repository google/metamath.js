include "wal.mm"
include "wi.mm"
include "wn.mm"
include "sp.mm"
include "con2i.mm"
include "hbn1.mm"
include "con1i.mm"
include "alimi.mm"
include "3syl.mm"
include "alim.mm"
include "syl5.mm"

theorem axc4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) )

  proof
    wph
    vx
    wal
    #
    @0
    vx
    wal
    #
    @0
    wps
    wi
    vx
    wal
    wps
    vx
    wal
    @0
    @0
    wn
    #
    vx
    wal
    #
    wn
    #
    @4
    vx
    wal
    @1
    @3
    @0
    @2
    vx
    sp
    con2i
    @2
    vx
    hbn1
    @4
    @0
    vx
    @0
    @3
    wph
    vx
    hbn1
    con1i
    alimi
    3syl
    @0
    wps
    vx
    alim
    syl5
end
