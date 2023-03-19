include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "weu.mm"
include "wrex.mm"
include "wi.mm"
include "c0.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "eunex.mm"
include "exnal.mm"
include "sylib.mm"
include "rzal.mm"
include "alrimiv.mm"
include "nsyl3.mm"
include "pm2.21d.mm"
include "wne.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "euex.mm"
include "eqeq1.mm"
include "ralbidv.mm"
include "cbvexv.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wcel.mm"
include "simprr.mm"
include "rspa.mm"
include "ad2ant2lr.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "exp32.mm"
include "rexlimd.mm"
include "r19.2z.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"
include "eubidv.mm"
include "exlimdv.mm"
include "syl5.mm"
include "imp.mm"
include "mpbird.mm"
include "pm2.61ine.mm"

theorem reusv2lem2OLD
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let cC: class C
  let wph: wff ph

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint ph x
  disjoint ph z
  assert |- ( E! x A. y e. A x = B -> E! x E. y e. A x = B )

  proof
    vx
    cv
    #
    cB
    wceq
    #
    vy
    cA
    wral
    #
    vx
    weu
    #
    @1
    vy
    cA
    wrex
    #
    vx
    weu
    #
    wi
    cA
    c0
    cA
    c0
    wceq
    #
    @3
    @5
    @3
    @2
    vx
    wal
    #
    @6
    @3
    @2
    wn
    vx
    wex
    @7
    wn
    @2
    vx
    eunex
    @2
    vx
    exnal
    sylib
    @6
    @2
    vx
    @1
    vy
    cA
    rzal
    alrimiv
    nsyl3
    pm2.21d
    cA
    c0
    wne
    #
    @3
    @5
    @8
    @3
    wa
    @5
    @3
    @8
    @3
    simpr
    @8
    @3
    @5
    @3
    wb
    #
    @3
    vz
    cv
    #
    cB
    wceq
    #
    vy
    cA
    wral
    #
    vz
    wex
    #
    @8
    @9
    @3
    @2
    vx
    wex
    @13
    @2
    vx
    euex
    @2
    @12
    vx
    vz
    @0
    @10
    wceq
    #
    @1
    @11
    vy
    cA
    @0
    @10
    cB
    eqeq1
    ralbidv
    #
    cbvexv
    sylib
    @8
    @12
    @9
    vz
    @8
    @12
    @9
    @8
    @12
    wa
    #
    @4
    @2
    vx
    @16
    @4
    @2
    @16
    @1
    @2
    vy
    cA
    @8
    @12
    vy
    @8
    vy
    nfv
    @11
    vy
    cA
    nfra1
    nfan
    @1
    vy
    cA
    nfra1
    @16
    vy
    cv
    cA
    wcel
    #
    @1
    @2
    @16
    @17
    @1
    wa
    #
    wa
    #
    @14
    @2
    @19
    @0
    cB
    @10
    @16
    @17
    @1
    simprr
    @12
    @17
    @11
    @8
    @1
    @11
    vy
    cA
    rspa
    ad2ant2lr
    eqtr4d
    @19
    @2
    @14
    @12
    @8
    @12
    @18
    simplr
    @15
    syl5ibrcom
    mpd
    exp32
    rexlimd
    @8
    @2
    @4
    wi
    @12
    @8
    @2
    @4
    @1
    vy
    cA
    r19.2z
    ex
    adantr
    impbid
    eubidv
    ex
    exlimdv
    syl5
    imp
    mpbird
    ex
    pm2.61ine
end
