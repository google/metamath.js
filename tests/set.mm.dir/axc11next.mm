include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wi.mm"
include "ax-ext.mm"
include "alimi.mm"
include "ax-11.mm"
include "ax9.mm"
include "biimpr.mm"
include "stdpc5v.mm"
include "syl.mm"
include "syl9.mm"
include "alimdv.mm"
include "syl5.mm"
include "sps.mm"
include "mpcom.mm"
include "axc4i.mm"
include "wex.mm"
include "nfa1.mm"
include "19.23.mm"
include "19.8a.mm"
include "elequ2.mm"
include "cbvexv.mm"
include "sylib.mm"
include "cbvalivw.mm"
include "imim12i.mm"
include "sylbi.mm"
include "alcoms.mm"
include "alrimiv.mm"
include "spimv.mm"
include "sp.mm"
include "impbid.mm"
include "3syl.mm"
include "axext4.mm"
include "albii.mm"
include "3imtr4i.mm"

theorem axc11next
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint w x
  disjoint w z
  assert |- ( A. x x = z -> A. z z = x )

  proof
    vw
    cv
    #
    vx
    cv
    #
    wcel
    #
    @0
    vz
    cv
    #
    wcel
    #
    wb
    #
    vw
    wal
    #
    vx
    wal
    #
    @4
    @2
    wb
    #
    vw
    wal
    #
    vz
    wal
    #
    @1
    @3
    wceq
    #
    vx
    wal
    #
    @3
    @1
    wceq
    #
    vz
    wal
    @7
    @2
    @2
    vx
    wal
    #
    wi
    #
    vw
    wal
    #
    vx
    wal
    #
    @4
    @4
    vz
    wal
    #
    wi
    #
    vw
    wal
    #
    vz
    wal
    @10
    @6
    @16
    vx
    @12
    @7
    @16
    @6
    @11
    vx
    vx
    vz
    vw
    ax-ext
    alimi
    @11
    @7
    @16
    wi
    vx
    @7
    @5
    vx
    wal
    #
    vw
    wal
    @11
    @16
    @5
    vx
    vw
    ax-11
    @11
    @21
    @15
    vw
    @11
    @2
    @4
    @21
    @14
    vx
    vz
    vw
    ax9
    #
    @21
    @4
    @2
    wi
    #
    vx
    wal
    @4
    @14
    wi
    @5
    @23
    vx
    @2
    @4
    biimpr
    alimi
    @4
    @2
    vx
    stdpc5v
    syl
    syl9
    alimdv
    syl5
    sps
    mpcom
    axc4i
    @17
    @20
    vz
    @15
    @20
    vw
    vx
    @15
    vx
    wal
    #
    @19
    vw
    @24
    @2
    vx
    wex
    #
    @14
    wi
    @19
    @2
    @14
    vx
    @2
    vx
    nfa1
    19.23
    @4
    @25
    @14
    @18
    @4
    @4
    vz
    wex
    #
    @25
    @4
    vz
    19.8a
    #
    @4
    @2
    vz
    vx
    vz
    vx
    vw
    elequ2
    cbvexv
    sylib
    @2
    @4
    vx
    vz
    @22
    cbvalivw
    imim12i
    sylbi
    alimi
    alcoms
    alrimiv
    @20
    @9
    vz
    @19
    @9
    vw
    vz
    @19
    vz
    wal
    #
    @8
    vw
    @28
    @26
    @18
    wi
    #
    @8
    @4
    @18
    vz
    @4
    vz
    nfa1
    19.23
    @29
    @4
    @2
    @4
    @26
    @18
    @2
    @27
    @4
    @2
    vz
    vx
    vz
    vx
    vw
    ax9
    spimv
    imim12i
    @2
    @26
    @18
    @4
    @2
    @25
    @26
    @2
    vx
    19.8a
    @2
    @4
    vx
    vz
    vx
    vz
    vw
    elequ2
    cbvexv
    sylib
    @4
    vz
    sp
    imim12i
    impbid
    sylbi
    alimi
    alcoms
    axc4i
    3syl
    @11
    @6
    vx
    vx
    vz
    vw
    axext4
    albii
    @13
    @9
    vz
    vz
    vx
    vw
    axext4
    albii
    3imtr4i
end
