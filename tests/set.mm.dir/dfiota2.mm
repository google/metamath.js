include "cio.mm"
include "cab.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "cuni.mm"
include "wb.mm"
include "wal.mm"
include "df-iota.mm"
include "df-sn.mm"
include "eqeq2i.mm"
include "abbi.mm"
include "bitr4i.mm"
include "abbii.mm"
include "unieqi.mm"
include "eqtri.mm"

theorem dfiota2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph y
  assert |- ( iota x ph ) = U. { y | A. x ( ph <-> x = y ) }

  proof
    wph
    vx
    cio
    wph
    vx
    cab
    #
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    cab
    #
    cuni
    wph
    vx
    cv
    @1
    wceq
    #
    wb
    vx
    wal
    #
    vy
    cab
    #
    cuni
    wph
    vx
    vy
    df-iota
    @4
    @7
    @3
    @6
    vy
    @3
    @0
    @5
    vx
    cab
    #
    wceq
    @6
    @2
    @8
    @0
    vx
    @1
    df-sn
    eqeq2i
    wph
    @5
    vx
    abbi
    bitr4i
    abbii
    unieqi
    eqtri
end
