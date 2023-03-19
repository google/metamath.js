include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "cioo.mm"
include "cpi.mm"
include "wrex.mm"
include "necomd.mm"
include "angpieqvd.mm"
include "mpbid.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "c2.mm"
include "cexp.mm"
include "ad2antrr.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "cc.mm"
include "cicc.mm"
include "ioossicc.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "chordthmlem5.mm"
include "simplrl.mm"
include "simplrr.mm"
include "3eqtr4d.mm"
include "rexlimddv.mm"

theorem chordthm
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
  assume chordthm.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume chordthm.A: |- ( ph -> A e. CC )
  assume chordthm.B: |- ( ph -> B e. CC )
  assume chordthm.C: |- ( ph -> C e. CC )
  assume chordthm.D: |- ( ph -> D e. CC )
  assume chordthm.P: |- ( ph -> P e. CC )
  assume chordthm.AneP: |- ( ph -> A =/= P )
  assume chordthm.BneP: |- ( ph -> B =/= P )
  assume chordthm.CneP: |- ( ph -> C =/= P )
  assume chordthm.DneP: |- ( ph -> D =/= P )
  assume chordthm.APB: |- ( ph -> ( ( A - P ) F ( B - P ) ) = _pi )
  assume chordthm.CPD: |- ( ph -> ( ( C - P ) F ( D - P ) ) = _pi )
  assume chordthm.Q: |- ( ph -> Q e. CC )
  assume chordthm.ABcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )
  assume chordthm.ACcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( C - Q ) ) )
  assume chordthm.ADcirc: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( D - Q ) ) )

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
    cP
    vv
    cv
    #
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
    vv
    cc0
    c1
    cioo
    co
    #
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
    @1
    vv
    @5
    wrex
    chordthm.CPD
    wph
    vx
    vy
    vv
    cC
    cP
    cD
    cF
    chordthm.angdef
    chordthm.C
    chordthm.P
    chordthm.D
    chordthm.CneP
    wph
    cD
    cP
    chordthm.DneP
    necomd
    angpieqvd
    mpbid
    wph
    @0
    @5
    wcel
    #
    @1
    wa
    #
    wa
    #
    cP
    vw
    cv
    #
    cA
    cmul
    co
    c1
    @9
    cmin
    co
    cB
    cmul
    co
    caddc
    co
    wceq
    #
    @4
    vw
    @5
    wph
    @10
    vw
    @5
    wrex
    #
    @7
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
    @11
    chordthm.APB
    wph
    vx
    vy
    vw
    cA
    cP
    cB
    cF
    chordthm.angdef
    chordthm.A
    chordthm.P
    chordthm.B
    chordthm.AneP
    wph
    cB
    cP
    chordthm.BneP
    necomd
    angpieqvd
    mpbid
    adantr
    @8
    @9
    @5
    wcel
    #
    @10
    wa
    #
    wa
    #
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
    @17
    cmin
    co
    @2
    @3
    @14
    @16
    @19
    @17
    cmin
    @14
    @15
    @18
    c2
    cexp
    @14
    cA
    cQ
    cmin
    co
    cabs
    cfv
    #
    @15
    @18
    wph
    @20
    @15
    wceq
    @7
    @13
    chordthm.ABcirc
    ad2antrr
    #
    wph
    @20
    @18
    wceq
    @7
    @13
    chordthm.ADcirc
    ad2antrr
    #
    eqtr3d
    oveq1d
    oveq1d
    @14
    cA
    cB
    cP
    cQ
    @9
    wph
    cA
    cc
    wcel
    @7
    @13
    chordthm.A
    ad2antrr
    wph
    cB
    cc
    wcel
    @7
    @13
    chordthm.B
    ad2antrr
    wph
    cQ
    cc
    wcel
    @7
    @13
    chordthm.Q
    ad2antrr
    #
    @14
    @5
    cc0
    c1
    cicc
    co
    #
    @9
    cc0
    c1
    ioossicc
    #
    @8
    @12
    @10
    simprl
    sseldi
    @8
    @12
    @10
    simprr
    @21
    chordthmlem5
    @14
    cC
    cD
    cP
    cQ
    @0
    wph
    cC
    cc
    wcel
    @7
    @13
    chordthm.C
    ad2antrr
    wph
    cD
    cc
    wcel
    @7
    @13
    chordthm.D
    ad2antrr
    @23
    @14
    @5
    @24
    @0
    @25
    wph
    @6
    @1
    @13
    simplrl
    sseldi
    wph
    @6
    @1
    @13
    simplrr
    @14
    @20
    cC
    cQ
    cmin
    co
    cabs
    cfv
    #
    @18
    wph
    @20
    @26
    wceq
    @7
    @13
    chordthm.ACcirc
    ad2antrr
    @22
    eqtr3d
    chordthmlem5
    3eqtr4d
    rexlimddv
    rexlimddv
end
