include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cnp.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "genpelv.mm"
include "syl5ibr.mm"

theorem genpprecl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
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
  assert |- ( ( A e. P. /\ B e. P. ) -> ( ( C e. A /\ D e. B ) -> ( C G D ) e. ( A F B ) ) )

  proof
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    wa
    cC
    cD
    cG
    co
    #
    cA
    cB
    cF
    co
    wcel
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    @2
    vg
    cv
    vh
    cv
    cG
    co
    wceq
    vh
    cB
    wrex
    vg
    cA
    wrex
    #
    @0
    @1
    @2
    @2
    wceq
    @3
    @2
    eqid
    vg
    vh
    cA
    cB
    cC
    cD
    @2
    cG
    rspceov
    mp3an3
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @2
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpelv
    syl5ibr
end
