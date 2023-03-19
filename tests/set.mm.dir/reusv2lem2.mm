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
include "nfra1.mm"
include "wcel.mm"
include "rspa.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "eqeq1.mm"
include "ralbidv.mm"
include "biimprcd.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "exp31.mm"
include "rexlimd.mm"
include "adantl.mm"
include "r19.2z.mm"
include "ex.mm"
include "impbid.mm"
include "eubidv.mm"
include "exlimdv.mm"
include "euex.mm"
include "cbvexv.mm"
include "impel.mm"
include "mpbird.mm"
include "pm2.61ine.mm"

theorem reusv2lem2
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
    @5
    @3
    wb
    #
    @3
    @8
    @11
    @13
    vz
    @8
    @11
    @13
    @8
    @11
    wa
    #
    @4
    @2
    vx
    @14
    @4
    @2
    @11
    @4
    @2
    wi
    @8
    @11
    @1
    @2
    vy
    cA
    @10
    vy
    cA
    nfra1
    @1
    vy
    cA
    nfra1
    @11
    vy
    cv
    cA
    wcel
    #
    @1
    @2
    @11
    @15
    wa
    #
    @1
    wa
    #
    @0
    @9
    wceq
    #
    @2
    @17
    @0
    cB
    @9
    @16
    @1
    simpr
    @16
    @10
    @1
    @10
    vy
    cA
    rspa
    adantr
    eqtr4d
    @11
    @18
    @2
    wi
    @15
    @1
    @18
    @2
    @11
    @18
    @1
    @10
    vy
    cA
    @0
    @9
    cB
    eqeq1
    ralbidv
    #
    biimprcd
    ad2antrr
    mpd
    exp31
    rexlimd
    adantl
    @8
    @2
    @4
    wi
    @11
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
    @3
    @2
    vx
    wex
    @12
    @2
    vx
    euex
    @2
    @11
    vx
    vz
    @19
    cbvexv
    sylib
    impel
    mpbird
    ex
    pm2.61ine
end
