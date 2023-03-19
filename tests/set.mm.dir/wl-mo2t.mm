include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wnf.mm"
include "mo2v.mm"
include "nfnf1.mm"
include "nfal.mm"
include "nfa1.mm"
include "sp.mm"
include "nfvd.mm"
include "nfimd.mm"
include "nfald.mm"
include "wb.mm"
include "equequ2.mm"
include "imbi2d.mm"
include "albidv.mm"
include "a1i.mm"
include "cbvexd.mm"
include "syl5bb.mm"

theorem wl-mo2t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint x y
  disjoint u x
  disjoint u y
  disjoint ph u
  assert |- ( A. x F/ y ph -> ( E* x ph <-> E. y A. x ( ph -> x = y ) ) )

  proof
    wph
    vx
    wmo
    wph
    vx
    vu
    weq
    #
    wi
    #
    vx
    wal
    #
    vu
    wex
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    vx
    vy
    weq
    #
    wi
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    vu
    mo2v
    @4
    @2
    @7
    vu
    vy
    @3
    vy
    vx
    wph
    vy
    nfnf1
    nfal
    @4
    @1
    vy
    vx
    @3
    vx
    nfa1
    @4
    wph
    @0
    vy
    @3
    vx
    sp
    @4
    @0
    vy
    nfvd
    nfimd
    nfald
    vu
    vy
    weq
    #
    @2
    @7
    wb
    wi
    @4
    @8
    @1
    @6
    vx
    @8
    @0
    @5
    wph
    vu
    vy
    vx
    equequ2
    imbi2d
    albidv
    a1i
    cbvexd
    syl5bb
end
