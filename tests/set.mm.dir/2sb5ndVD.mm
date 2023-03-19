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
include "hbs1.mm"
include "idn1.mm"
include "axc11.mm"
include "e1a.mm"
include "imim1.mm"
include "e01.mm"
include "in1.mm"
include "sbt.mm"
include "sbi1.mm"
include "e0a.mm"
include "axc11n.mm"
include "con3i.mm"
include "sbal2.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "pm2.61i.mm"
include "nf5i.mm"
include "19.41.mm"
include "bitr3i.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "pm5.32.mm"
include "mpbir.mm"
include "sylbi.mm"

theorem 2sb5ndVD
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
    #
    wn
    #
    vu
    cv
    #
    vv
    cv
    #
    wceq
    wo
    @0
    @4
    wceq
    @1
    @5
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
    @6
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
    @8
    @14
    wi
    @8
    @10
    wa
    #
    @8
    @13
    wa
    #
    wb
    @15
    @8
    @15
    wa
    @16
    @8
    @10
    anabs5
    @15
    @13
    @8
    @13
    @7
    @10
    wa
    #
    vx
    wex
    @15
    @12
    @17
    vx
    @12
    @6
    @10
    wa
    #
    vy
    wex
    @17
    @18
    @11
    vy
    wph
    vx
    vy
    vv
    vu
    2pm13.193
    exbii
    @6
    @10
    vy
    @10
    vy
    @2
    @10
    @10
    vy
    wal
    #
    wi
    #
    @2
    @20
    @10
    @10
    vx
    wal
    #
    wi
    @2
    @21
    @19
    wi
    #
    @20
    @9
    vx
    vu
    hbs1
    #
    @2
    @2
    @22
    @2
    idn1
    @10
    vx
    vy
    axc11
    e1a
    @10
    @21
    @19
    imim1
    e01
    in1
    @3
    @20
    @10
    @9
    vy
    wal
    #
    vx
    vu
    wsb
    #
    wi
    #
    @3
    @25
    @19
    wb
    #
    @20
    @9
    @24
    wi
    #
    vx
    vu
    wsb
    @26
    @28
    vx
    vu
    wph
    vy
    vv
    hbs1
    sbt
    @9
    @24
    vx
    vu
    sbi1
    e0a
    @3
    @1
    @0
    wceq
    vy
    wal
    #
    wn
    #
    @27
    @3
    @3
    @30
    @3
    idn1
    @29
    @2
    vy
    vx
    axc11n
    con3i
    e1a
    @9
    vy
    vx
    vu
    sbal2
    e1a
    @27
    @26
    @20
    @25
    @19
    @10
    imbi2
    biimpcd
    e01
    in1
    pm2.61i
    nf5i
    19.41
    bitr3i
    exbii
    @7
    @10
    vx
    @10
    vx
    @23
    nf5i
    19.41
    bitr2i
    anbi2i
    bitr3i
    @8
    @10
    @13
    pm5.32
    mpbir
    sylbi
end
