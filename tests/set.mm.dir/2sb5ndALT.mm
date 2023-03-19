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
include "id.mm"
include "axc11.mm"
include "syl.mm"
include "pm3.33.mm"
include "sylancr.mm"
include "sbt.mm"
include "sbi1.mm"
include "ax-mp.mm"
include "axc11n.mm"
include "con3i.mm"
include "sbal2.mm"
include "imbi2.mm"
include "biimpac.mm"
include "pm2.61i.mm"
include "nf5i.mm"
include "19.41.mm"
include "bitr3i.mm"
include "nfs1v.mm"
include "bitr2i.mm"
include "anbi2i.mm"
include "pm5.32.mm"
include "mpbir.mm"
include "sylbi.mm"

theorem 2sb5ndALT
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
    @10
    @10
    vx
    wal
    #
    wi
    @21
    @19
    wi
    #
    @20
    @9
    vx
    vu
    hbs1
    @2
    @2
    @22
    @2
    id
    @10
    vx
    vy
    axc11
    syl
    @10
    @21
    @19
    pm3.33
    sylancr
    @3
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
    @24
    @19
    wb
    #
    @20
    @9
    @23
    wi
    #
    vx
    vu
    wsb
    @25
    @27
    vx
    vu
    wph
    vy
    vv
    hbs1
    sbt
    @9
    @23
    vx
    vu
    sbi1
    ax-mp
    @3
    @1
    @0
    wceq
    vy
    wal
    #
    wn
    #
    @26
    @3
    @3
    @29
    @3
    id
    @28
    @2
    vy
    vx
    axc11n
    con3i
    syl
    @9
    vy
    vx
    vu
    sbal2
    syl
    @26
    @25
    @20
    @24
    @19
    @10
    imbi2
    biimpac
    sylancr
    pm2.61i
    nf5i
    19.41
    bitr3i
    exbii
    @7
    @10
    vx
    @9
    vx
    vu
    nfs1v
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
