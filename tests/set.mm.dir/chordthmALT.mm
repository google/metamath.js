include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cabs.mm"
include "cfv.mm"
include "wrex.mm"
include "cpi.mm"
include "necomd.mm"
include "angpieqvd.mm"
include "mpbid.mm"
include "df-rex.mm"
include "biimpi.mm"
include "syl.mm"
include "adantr.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "cc.mm"
include "cicc.mm"
include "ioossicc.mm"
include "id.mm"
include "sseldi.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "chordthmlem5.mm"
include "3expb.mm"
include "3adant2.mm"
include "3adant3.mm"
include "3eqtr4d.mm"
include "3expia.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ex.mm"

theorem chordthmALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cF: class F
  let vv: setvar v
  let vw: setvar w
  assume chordthmALT.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume chordthmALT.A: |- ( ph -> A e. CC )
  assume chordthmALT.B: |- ( ph -> B e. CC )
  assume chordthmALT.C: |- ( ph -> C e. CC )
  assume chordthmALT.D: |- ( ph -> D e. CC )
  assume chordthmALT.P: |- ( ph -> P e. CC )
  assume chordthmALT.AneP: |- ( ph -> A =/= P )
  assume chordthmALT.BneP: |- ( ph -> B =/= P )
  assume chordthmALT.CneP: |- ( ph -> C =/= P )
  assume chordthmALT.DneP: |- ( ph -> D =/= P )
  assume chordthmALT.APB: |- ( ph -> ( ( A - P ) F ( B - P ) ) = _pi )
  assume chordthmALT.CPD: |- ( ph -> ( ( C - P ) F ( D - P ) ) = _pi )
  assume chordthmALT.Q: |- ( ph -> Q e. CC )
  assume chordthmALT.ABcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )
  assume chordthmALT.ACcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( C - Q ) ) )
  assume chordthmALT.ADcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( D - Q ) ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint P x
  disjoint P y
  disjoint A v
  disjoint A w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint B v
  disjoint B w
  disjoint C v
  disjoint C w
  disjoint D v
  disjoint D w
  disjoint F v
  disjoint F w
  disjoint ph v
  disjoint ph w
  disjoint P v
  disjoint P w
  assert |- ( ph -> ( ( abs ` ( P - A ) ) x. ( abs ` ( P - B ) ) ) = ( ( abs ` ( P - C ) ) x. ( abs ` ( P - D ) ) ) )

  proof
    wph
    vv
    cv
    #
    cc0
    c1
    cioo
    co
    #
    wcel
    #
    cP
    @0
    cC
    cmul
    co
    c1
    @0
    cmin
    co
    cD
    cmul
    co
    caddc
    co
    wceq
    #
    wa
    #
    vv
    wex
    #
    cP
    cA
    cmin
    co
    cabs
    cfv
    cP
    cB
    cmin
    co
    cabs
    cfv
    cmul
    co
    #
    cP
    cC
    cmin
    co
    cabs
    cfv
    cP
    cD
    cmin
    co
    cabs
    cfv
    cmul
    co
    #
    wceq
    #
    wph
    @3
    vv
    @1
    wrex
    #
    @5
    wph
    cC
    cP
    cmin
    co
    cD
    cP
    cmin
    co
    cF
    co
    cpi
    wceq
    @9
    chordthmALT.CPD
    wph
    vx
    vy
    vv
    cC
    cP
    cD
    cF
    chordthmALT.angdef
    chordthmALT.C
    chordthmALT.P
    chordthmALT.D
    chordthmALT.CneP
    wph
    cD
    cP
    chordthmALT.DneP
    necomd
    angpieqvd
    mpbid
    @9
    @5
    @3
    vv
    @1
    df-rex
    biimpi
    syl
    wph
    @4
    @8
    vv
    wph
    @4
    @8
    wph
    @4
    wa
    #
    vw
    cv
    #
    @1
    wcel
    #
    cP
    @11
    cA
    cmul
    co
    c1
    @11
    cmin
    co
    cB
    cmul
    co
    caddc
    co
    wceq
    #
    wa
    #
    vw
    wex
    #
    @8
    wph
    @15
    @4
    wph
    @13
    vw
    @1
    wrex
    #
    @15
    wph
    cA
    cP
    cmin
    co
    cB
    cP
    cmin
    co
    cF
    co
    cpi
    wceq
    @16
    chordthmALT.APB
    wph
    vx
    vy
    vw
    cA
    cP
    cB
    cF
    chordthmALT.angdef
    chordthmALT.A
    chordthmALT.P
    chordthmALT.B
    chordthmALT.AneP
    wph
    cB
    cP
    chordthmALT.BneP
    necomd
    angpieqvd
    mpbid
    @16
    @15
    @13
    vw
    @1
    df-rex
    biimpi
    syl
    adantr
    @10
    @14
    @8
    vw
    wph
    @4
    @14
    @8
    wph
    @4
    @14
    w3a
    cB
    cQ
    cmin
    co
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cP
    cQ
    cmin
    co
    cabs
    cfv
    c2
    cexp
    co
    #
    cmin
    co
    #
    cD
    cQ
    cmin
    co
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @19
    cmin
    co
    #
    @6
    @7
    wph
    @4
    @20
    @23
    wceq
    @14
    wph
    @18
    @22
    @19
    cmin
    wph
    @17
    @21
    c2
    cexp
    wph
    cA
    cQ
    cmin
    co
    cabs
    cfv
    #
    @17
    @21
    chordthmALT.ABcirc
    chordthmALT.ADcirc
    eqtr3d
    oveq1d
    oveq1d
    3ad2ant1
    wph
    @14
    @6
    @20
    wceq
    #
    @4
    wph
    @12
    @13
    @25
    wph
    @12
    @13
    w3a
    cA
    cB
    cP
    cQ
    @11
    wph
    @12
    cA
    cc
    wcel
    @13
    chordthmALT.A
    3ad2ant1
    wph
    @12
    cB
    cc
    wcel
    @13
    chordthmALT.B
    3ad2ant1
    wph
    @12
    cQ
    cc
    wcel
    #
    @13
    chordthmALT.Q
    3ad2ant1
    @12
    wph
    @11
    cc0
    c1
    cicc
    co
    #
    wcel
    @13
    @12
    @1
    @27
    @11
    cc0
    c1
    ioossicc
    #
    @12
    id
    sseldi
    3ad2ant2
    @13
    wph
    @13
    @12
    @13
    id
    3ad2ant3
    wph
    @12
    @24
    @17
    wceq
    @13
    chordthmALT.ABcirc
    3ad2ant1
    chordthmlem5
    3expb
    3adant2
    wph
    @4
    @7
    @23
    wceq
    #
    @14
    wph
    @2
    @3
    @29
    wph
    @2
    @3
    w3a
    cC
    cD
    cP
    cQ
    @0
    wph
    @2
    cC
    cc
    wcel
    @3
    chordthmALT.C
    3ad2ant1
    wph
    @2
    cD
    cc
    wcel
    @3
    chordthmALT.D
    3ad2ant1
    wph
    @2
    @26
    @3
    chordthmALT.Q
    3ad2ant1
    @2
    wph
    @0
    @27
    wcel
    @3
    @2
    @1
    @27
    @0
    @28
    @2
    id
    sseldi
    3ad2ant2
    @3
    wph
    @3
    @2
    @3
    id
    3ad2ant3
    wph
    @2
    cC
    cQ
    cmin
    co
    cabs
    cfv
    #
    @21
    wceq
    @3
    wph
    @24
    @30
    @21
    chordthmALT.ACcirc
    chordthmALT.ADcirc
    eqtr3d
    3ad2ant1
    chordthmlem5
    3expb
    3adant3
    3eqtr4d
    3expia
    exlimdv
    mpd
    ex
    exlimdv
    mpd
end
