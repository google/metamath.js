include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "axc11n.mm"
include "nfe1.mm"
include "19.9.mm"
include "excom.mm"
include "nfa1.mm"
include "id.mm"
include "biid.mm"
include "a1i.mm"
include "drex1.mm"
include "syl.mm"
include "alrimi.mm"
include "exbi.mm"
include "bitr.mm"
include "ex.mm"
include "impcom.mm"
include "sylancr.mm"
include "bitr3.mm"

theorem e2ebindALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> ( E. x E. y ph <-> E. y ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vy
    vx
    weq
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
    @2
    wb
    #
    vx
    vy
    axc11n
    @1
    @2
    vy
    wex
    #
    @2
    wb
    #
    @5
    @3
    wb
    #
    @4
    @2
    vy
    wph
    vy
    nfe1
    19.9
    @1
    wph
    vx
    wex
    #
    vy
    wex
    #
    @3
    wb
    #
    @5
    @9
    wb
    #
    @7
    wph
    vy
    vx
    excom
    @1
    @2
    @8
    wb
    #
    vy
    wal
    @11
    @1
    @12
    vy
    @0
    vy
    nfa1
    @1
    @1
    @12
    @1
    id
    wph
    wph
    vy
    vx
    wph
    wph
    wb
    @1
    wph
    biid
    a1i
    drex1
    syl
    alrimi
    @2
    @8
    vy
    exbi
    syl
    @11
    @10
    @7
    @11
    @10
    @7
    @5
    @9
    @3
    bitr
    ex
    impcom
    sylancr
    @7
    @6
    @4
    @5
    @3
    @2
    bitr3
    impcom
    sylancr
    syl
end
