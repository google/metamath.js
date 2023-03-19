include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cnq.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "genpelv.mm"
include "wi.mm"
include "elprnq.mm"
include "ex.mm"
include "im2anan9.mm"
include "caovcl.mm"
include "syl6.mm"
include "eleq1a.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem genpss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
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
  disjoint G w
  disjoint G v
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint f v
  disjoint g v
  disjoint h v
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
  assert |- ( ( A e. P. /\ B e. P. ) -> ( A F B ) C_ Q. )

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
    cA
    cB
    cF
    co
    #
    cnq
    @2
    vf
    cv
    #
    @3
    wcel
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
    @4
    cnq
    wcel
    #
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
    @2
    @8
    @9
    vg
    vh
    cA
    cB
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
    @7
    cnq
    wcel
    #
    @8
    @9
    wi
    @2
    @12
    @5
    cnq
    wcel
    #
    @6
    cnq
    wcel
    #
    wa
    @13
    @0
    @10
    @14
    @1
    @11
    @15
    @0
    @10
    @14
    cA
    @5
    elprnq
    ex
    @1
    @11
    @15
    cB
    @6
    elprnq
    ex
    im2anan9
    vy
    vz
    @5
    @6
    cnq
    cG
    genp.2
    caovcl
    syl6
    @7
    cnq
    @4
    eleq1a
    syl6
    rexlimdvv
    sylbid
    ssrdv
end
