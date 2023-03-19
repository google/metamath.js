include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wnf.mm"
include "notnotb.mm"
include "albii.mm"
include "orbi1i.mm"
include "orcom.mm"
include "bitri.mm"
include "nf3.mm"
include "3bitr4i.mm"

theorem nfnbi
  let wph: wff ph
  let vx: setvar x


  assert |- ( F/ x ph <-> F/ x -. ph )

  proof
    wph
    vx
    wal
    #
    wph
    wn
    #
    vx
    wal
    #
    wo
    #
    @2
    @1
    wn
    #
    vx
    wal
    #
    wo
    #
    wph
    vx
    wnf
    @1
    vx
    wnf
    @3
    @5
    @2
    wo
    @6
    @0
    @5
    @2
    wph
    @4
    vx
    wph
    notnotb
    albii
    orbi1i
    @5
    @2
    orcom
    bitri
    wph
    vx
    nf3
    @1
    vx
    nf3
    3bitr4i
end
