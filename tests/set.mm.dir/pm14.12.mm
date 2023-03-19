include "weu.mm"
include "wmo.mm"
include "cv.mm"
include "wsbc.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eumo.mm"
include "wsb.mm"
include "nfv.mm"
include "mo3.mm"
include "sbsbc.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "2albii.mm"
include "bitri.mm"
include "sylib.mm"

theorem pm14.12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint x y
  assert |- ( E! x ph -> A. x A. y ( ( ph /\ [. y / x ]. ph ) -> x = y ) )

  proof
    wph
    vx
    weu
    wph
    vx
    wmo
    #
    wph
    wph
    vx
    vy
    cv
    wsbc
    #
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wph
    vx
    eumo
    @0
    wph
    wph
    vx
    vy
    wsb
    #
    wa
    #
    @3
    wi
    #
    vy
    wal
    vx
    wal
    @5
    wph
    vx
    vy
    wph
    vy
    nfv
    mo3
    @8
    @4
    vx
    vy
    @7
    @2
    @3
    @6
    @1
    wph
    wph
    vx
    vy
    sbsbc
    anbi2i
    imbi1i
    2albii
    bitri
    sylib
end
