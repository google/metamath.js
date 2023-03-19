include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "co.mm"
include "wi.mm"
include "cnq.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simpld.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "genpelv.mm"
include "adantr.mm"
include "breq2.mm"
include "biimpd.mm"
include "sylan9r.mm"
include "exp31.mm"
include "an4s.mm"
include "impancom.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "ex.mm"
include "syl5.mm"
include "com34.mm"
include "pm2.43d.mm"
include "com23.mm"

theorem genpcd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )
  assume genpcd.2: |- ( ( ( ( A e. P. /\ g e. A ) /\ ( B e. P. /\ h e. B ) ) /\ x e. Q. ) -> ( x <Q ( g G h ) -> x e. ( A F B ) ) )

  disjoint F h
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint A x
  disjoint y z
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint A y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint B g
  disjoint B h
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
  disjoint g w
  disjoint h w
  disjoint G w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint G v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint F f
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint D g
  disjoint D h
  assert |- ( ( A e. P. /\ B e. P. ) -> ( f e. ( A F B ) -> ( x <Q f -> x e. ( A F B ) ) ) )

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
    vx
    cv
    #
    vf
    cv
    #
    cltq
    wbr
    #
    @4
    cA
    cB
    cF
    co
    #
    wcel
    #
    @3
    @6
    wcel
    #
    @2
    @5
    @7
    @8
    wi
    @2
    @5
    @7
    @5
    @8
    @5
    @3
    cnq
    wcel
    #
    @2
    @7
    @5
    @8
    wi
    #
    wi
    #
    @5
    @9
    @4
    cnq
    wcel
    @3
    @4
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    @2
    @9
    @11
    @2
    @9
    wa
    #
    @7
    @4
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
    #
    @10
    @2
    @7
    @17
    wb
    @9
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @4
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpelv
    adantr
    @12
    @16
    @10
    vg
    vh
    cA
    cB
    @2
    @13
    cA
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    @9
    @16
    @10
    wi
    #
    @0
    @18
    @1
    @19
    @9
    @20
    wi
    @0
    @18
    wa
    @1
    @19
    wa
    wa
    #
    @9
    @16
    @10
    @16
    @5
    @3
    @15
    cltq
    wbr
    #
    @21
    @9
    wa
    @8
    @16
    @5
    @22
    @4
    @15
    @3
    cltq
    breq2
    biimpd
    genpcd.2
    sylan9r
    exp31
    an4s
    impancom
    rexlimdvv
    sylbid
    ex
    syl5
    com34
    pm2.43d
    com23
end
