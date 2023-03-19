include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "axc11n.mm"
include "hba1.mm"
include "idn1.mm"
include "biid.mm"
include "a1i.mm"
include "drex1.mm"
include "e1a.mm"
include "gen11nv.mm"
include "exbi.mm"
include "excom.mm"
include "bibi1.mm"
include "biimprd.mm"
include "e10.mm"
include "nfe1.mm"
include "19.9.mm"
include "bitr3.mm"
include "in1.mm"
include "syl.mm"

theorem e2ebindVD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) )

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
    @1
    @0
    wceq
    #
    vy
    wal
    #
    wph
    vy
    wex
    #
    vx
    wex
    #
    @4
    wb
    #
    vx
    vy
    axc11n
    @3
    @6
    @3
    @4
    vy
    wex
    #
    @5
    wb
    #
    @7
    @4
    wb
    @6
    @3
    @7
    wph
    vx
    wex
    #
    vy
    wex
    #
    wb
    #
    @10
    @5
    wb
    #
    @8
    @3
    @4
    @9
    wb
    #
    vy
    wal
    @11
    @3
    @13
    vy
    @2
    vy
    hba1
    @3
    @3
    @13
    @3
    idn1
    wph
    wph
    vy
    vx
    wph
    wph
    wb
    @3
    wph
    biid
    a1i
    drex1
    e1a
    gen11nv
    @4
    @9
    vy
    exbi
    e1a
    wph
    vy
    vx
    excom
    @11
    @8
    @12
    @7
    @10
    @5
    bibi1
    biimprd
    e10
    @4
    vy
    wph
    vy
    nfe1
    19.9
    @7
    @5
    @4
    bitr3
    e10
    in1
    syl
end
