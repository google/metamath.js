include "wnf.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "wn.mm"
include "wb.mm"
include "wl-nfnbi.mm"
include "albii.mm"
include "wl-sb8t.mm"
include "sylbi.mm"
include "alnex.mm"
include "sbn.mm"
include "bitri.mm"
include "3bitr3g.mm"
include "con4bid.mm"

theorem wl-sb8et
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> ( E. x ph <-> E. y [ y / x ] ph ) )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    vx
    wex
    #
    wph
    vx
    vy
    wsb
    #
    vy
    wex
    #
    @1
    wph
    wn
    #
    vx
    wal
    #
    @5
    vx
    vy
    wsb
    #
    vy
    wal
    #
    @2
    wn
    @4
    wn
    #
    @1
    @5
    vy
    wnf
    #
    vx
    wal
    @6
    @8
    wb
    @0
    @10
    vx
    wph
    vy
    wl-nfnbi
    albii
    @5
    vx
    vy
    wl-sb8t
    sylbi
    wph
    vx
    alnex
    @8
    @3
    wn
    #
    vy
    wal
    @9
    @7
    @11
    vy
    wph
    vx
    vy
    sbn
    albii
    @3
    vy
    alnex
    bitri
    3bitr3g
    con4bid
end
