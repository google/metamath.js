include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wex.mm"
include "wsb.mm"
include "wb.mm"
include "ax6e2ndeq.mm"
include "wi.mm"
include "anabs5.mm"
include "2pm13.193.mm"
include "exbii.mm"
include "nfs1v.mm"
include "nfsb.mm"
include "19.41.mm"
include "bitr3i.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "pm5.32.mm"
include "mpbir.mm"
include "sylbi.mm"

theorem 2sb5nd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( -. A. x x = y \/ u = v ) -> ( [ u / x ] [ v / y ] ph <-> E. x E. y ( ( x = u /\ y = v ) /\ ph ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    vx
    wal
    wn
    vu
    cv
    #
    vv
    cv
    #
    wceq
    wo
    @0
    @2
    wceq
    @1
    @3
    wceq
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wph
    vy
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @4
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wb
    #
    vx
    vy
    vv
    vu
    ax6e2ndeq
    @6
    @12
    wi
    @6
    @8
    wa
    #
    @6
    @11
    wa
    #
    wb
    @13
    @6
    @13
    wa
    @14
    @6
    @8
    anabs5
    @13
    @11
    @6
    @11
    @5
    @8
    wa
    #
    vx
    wex
    @13
    @10
    @15
    vx
    @10
    @4
    @8
    wa
    #
    vy
    wex
    @15
    @16
    @9
    vy
    wph
    vx
    vy
    vv
    vu
    2pm13.193
    exbii
    @4
    @8
    vy
    @7
    vx
    vu
    vy
    wph
    vy
    vv
    nfs1v
    nfsb
    19.41
    bitr3i
    exbii
    @5
    @8
    vx
    @7
    vx
    vu
    nfs1v
    19.41
    bitr2i
    anbi2i
    bitr3i
    @6
    @8
    @11
    pm5.32
    mpbir
    sylbi
end
