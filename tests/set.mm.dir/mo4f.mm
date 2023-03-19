include "wmo.mm"
include "wsb.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "mo3.mm"
include "sbie.mm"
include "anbi2i.mm"
include "imbi1i.mm"
include "2albii.mm"
include "bitri.mm"

theorem mo4f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume mo4f.1: |- F/ x ps
  assume mo4f.2: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  assert |- ( E* x ph <-> A. x A. y ( ( ph /\ ps ) -> x = y ) )

  proof
    wph
    vx
    wmo
    wph
    wph
    vx
    vy
    wsb
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
    wph
    wps
    wa
    #
    @2
    wi
    #
    vy
    wal
    vx
    wal
    wph
    vx
    vy
    wph
    vy
    nfv
    mo3
    @3
    @5
    vx
    vy
    @1
    @4
    @2
    @0
    wps
    wph
    wph
    wps
    vx
    vy
    mo4f.1
    mo4f.2
    sbie
    anbi2i
    imbi1i
    2albii
    bitri
end
