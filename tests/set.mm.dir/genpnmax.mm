include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cltq.mm"
include "wbr.mm"
include "genpelv.mm"
include "prnmax.mm"
include "adantr.mm"
include "wi.mm"
include "genpprecl.mm"
include "exp4b.mm"
include "com34.mm"
include "imp32.mm"
include "cnq.mm"
include "elprnq.mm"
include "vex.mm"
include "caovord2.mm"
include "biimpd.mm"
include "syl.mm"
include "adantl.mm"
include "anim12d.mm"
include "breq2.mm"
include "rspcev.mm"
include "syl6.mm"
include "adantlr.mm"
include "expd.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "an4s.mm"
include "breq1.mm"
include "rexbidv.mm"
include "syl5ibr.mm"
include "expdcom.mm"
include "rexlimdvv.mm"
include "sylbid.mm"

theorem genpnmax
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let vh: setvar h
  let vg: setvar g
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )
  assume genpnmax.2: |- ( v e. Q. -> ( z <Q w <-> ( v G z ) <Q ( v G w ) ) )
  assume genpnmax.3: |- ( z G w ) = ( w G z )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint A x
  disjoint y z
  disjoint f y
  disjoint A y
  disjoint f z
  disjoint A z
  disjoint A f
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint w x
  disjoint v x
  disjoint G x
  disjoint w y
  disjoint v y
  disjoint G y
  disjoint w z
  disjoint v z
  disjoint G z
  disjoint v w
  disjoint f w
  disjoint G w
  disjoint f v
  disjoint G v
  disjoint G f
  disjoint F f
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint g x
  disjoint h x
  disjoint g y
  disjoint h y
  disjoint g z
  disjoint h z
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B g
  disjoint B h
  disjoint g w
  disjoint h w
  disjoint g v
  disjoint h v
  disjoint G g
  disjoint G h
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint D g
  disjoint D h
  assert |- ( ( A e. P. /\ B e. P. ) -> ( f e. ( A F B ) -> E. x e. ( A F B ) f <Q x ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    vf
    cv
    #
    cA
    cB
    cF
    co
    #
    wcel
    @3
    vg
    cv
    #
    vh
    cv
    #
    cG
    co
    #
    wceq
    #
    vh
    cB
    wrex
    vg
    cA
    wrex
    @3
    vx
    cv
    #
    cltq
    wbr
    #
    vx
    @4
    wrex
    #
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @3
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpelv
    @2
    @8
    @11
    vg
    vh
    cA
    cB
    @8
    @2
    @5
    cA
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    @11
    @2
    @14
    wa
    @11
    @8
    @7
    @9
    cltq
    wbr
    #
    vx
    @4
    wrex
    #
    @0
    @12
    @1
    @13
    @16
    @0
    @12
    wa
    #
    @1
    @13
    wa
    #
    wa
    #
    @5
    vy
    cv
    #
    cltq
    wbr
    #
    vy
    cA
    wrex
    #
    @16
    @17
    @22
    @18
    vy
    cA
    @5
    prnmax
    adantr
    @19
    @21
    @16
    vy
    cA
    @19
    @20
    cA
    wcel
    #
    @21
    @16
    @0
    @18
    @23
    @21
    wa
    #
    @16
    wi
    @12
    @0
    @18
    wa
    #
    @24
    @20
    @6
    cG
    co
    #
    @4
    wcel
    #
    @7
    @26
    cltq
    wbr
    #
    wa
    @16
    @25
    @23
    @27
    @21
    @28
    @0
    @1
    @13
    @23
    @27
    wi
    @0
    @1
    @23
    @13
    @27
    @0
    @1
    @23
    @13
    @27
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @20
    @6
    cF
    cG
    genp.1
    genp.2
    genpprecl
    exp4b
    com34
    imp32
    @18
    @21
    @28
    wi
    #
    @0
    @18
    @6
    cnq
    wcel
    #
    @29
    cB
    @6
    elprnq
    @30
    @21
    @28
    vz
    vw
    vv
    @5
    @20
    @6
    cltq
    cnq
    cG
    vg
    vex
    vy
    vex
    genpnmax.2
    vh
    vex
    genpnmax.3
    caovord2
    biimpd
    syl
    adantl
    anim12d
    @15
    @28
    vx
    @26
    @4
    @9
    @26
    @7
    cltq
    breq2
    rspcev
    syl6
    adantlr
    expd
    rexlimdv
    mpd
    an4s
    @8
    @10
    @15
    vx
    @4
    @3
    @7
    @9
    cltq
    breq1
    rexbidv
    syl5ibr
    expdcom
    rexlimdvv
    sylbid
end
