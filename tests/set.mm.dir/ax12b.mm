include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "axc15.mm"
include "imp.mm"
include "sp.mm"
include "com12.mm"
include "adantl.mm"
include "impbid.mm"

theorem ax12b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( -. A. x x = y /\ x = y ) -> ( ph <-> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @0
    wa
    wph
    @0
    wph
    wi
    #
    vx
    wal
    #
    @1
    @0
    wph
    @3
    wi
    wph
    vx
    vy
    axc15
    imp
    @0
    @3
    wph
    wi
    @1
    @3
    @0
    wph
    @2
    vx
    sp
    com12
    adantl
    impbid
end
