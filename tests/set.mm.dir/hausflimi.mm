include "cha.mm"
include "wcel.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "w3a.mm"
include "wrex.mm"
include "cuni.mm"
include "simpl.mm"
include "simprll.mm"
include "eqid.mm"
include "flimelbas.mm"
include "syl.mm"
include "simprlr.mm"
include "simprr.mm"
include "hausnei.mm"
include "syl13anc.mm"
include "df-3an.mm"
include "simprl.mm"
include "hausflimlem.mm"
include "3expa.mm"
include "sylanl1.mm"
include "a1d.mm"
include "necon4d.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "expr.mm"
include "necon1bd.mm"
include "pm2.18d.mm"
include "ex.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "mo4.mm"
include "sylibr.mm"

theorem hausflimi
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  let cX: class X

  disjoint F x
  disjoint J x
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint x y
  disjoint F y
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J f
  disjoint u w
  disjoint u z
  disjoint J u
  disjoint v w
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint S x
  disjoint S y
  disjoint X f
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X z
  assert |- ( J e. Haus -> E* x x e. ( J fLim F ) )

  proof
    cJ
    cha
    wcel
    #
    vx
    cv
    #
    cJ
    cF
    cflim
    co
    #
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    @1
    @4
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @3
    vx
    wmo
    @0
    @8
    vx
    vy
    @0
    @6
    @7
    @0
    @6
    wa
    #
    @7
    @9
    @7
    @1
    @4
    @0
    @6
    @1
    @4
    wne
    #
    @7
    @0
    @6
    @10
    wa
    #
    wa
    #
    @1
    vu
    cv
    #
    wcel
    #
    @4
    vv
    cv
    #
    wcel
    #
    @13
    @15
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vv
    cJ
    wrex
    vu
    cJ
    wrex
    #
    @7
    @12
    @0
    @1
    cJ
    cuni
    #
    wcel
    #
    @4
    @21
    wcel
    #
    @10
    @20
    @0
    @11
    simpl
    @12
    @3
    @22
    @0
    @3
    @5
    @10
    simprll
    @1
    cF
    cJ
    @21
    @21
    eqid
    #
    flimelbas
    syl
    @12
    @5
    @23
    @0
    @3
    @5
    @10
    simprlr
    @4
    cF
    cJ
    @21
    @24
    flimelbas
    syl
    @0
    @6
    @10
    simprr
    @1
    @4
    vv
    vu
    cJ
    @21
    @24
    hausnei
    syl13anc
    @12
    @19
    @7
    vu
    vv
    cJ
    cJ
    @19
    @14
    @16
    wa
    #
    @18
    wa
    @12
    @13
    cJ
    wcel
    @15
    cJ
    wcel
    wa
    #
    wa
    #
    @7
    @14
    @16
    @18
    df-3an
    @27
    @25
    @18
    @7
    @27
    @25
    wa
    #
    @1
    @4
    @17
    c0
    @28
    @17
    c0
    wne
    #
    @10
    @12
    @6
    @26
    @25
    @29
    @0
    @6
    @10
    simprl
    @6
    @26
    @25
    @29
    @1
    @4
    @13
    cF
    cJ
    @15
    hausflimlem
    3expa
    sylanl1
    a1d
    necon4d
    expimpd
    syl5bi
    rexlimdvva
    mpd
    expr
    necon1bd
    pm2.18d
    ex
    alrimivv
    @3
    @5
    vx
    vy
    @1
    @4
    @2
    eleq1
    mo4
    sylibr
end
