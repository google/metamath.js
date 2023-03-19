include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "c0.mm"
include "co.mm"
include "wpss.mm"
include "wne.mm"
include "prn0.mm"
include "n0.mm"
include "sylib.mm"
include "anim12i.mm"
include "wi.mm"
include "genpprecl.mm"
include "ne0i.mm"
include "0pss.mm"
include "sylibr.mm"
include "syl6.mm"
include "expcomd.mm"
include "exlimdv.mm"
include "com23.mm"
include "impd.mm"
include "mpd.mm"

theorem genpn0
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
  assert |- ( ( A e. P. /\ B e. P. ) -> (/) C. ( A F B ) )

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
    wcel
    #
    vf
    wex
    #
    vg
    cv
    #
    cB
    wcel
    #
    vg
    wex
    #
    wa
    c0
    cA
    cB
    cF
    co
    #
    wpss
    #
    @0
    @5
    @1
    @8
    @0
    cA
    c0
    wne
    @5
    cA
    prn0
    vf
    cA
    n0
    sylib
    @1
    cB
    c0
    wne
    @8
    cB
    prn0
    vg
    cB
    n0
    sylib
    anim12i
    @2
    @5
    @8
    @10
    @2
    @4
    @8
    @10
    wi
    vf
    @2
    @8
    @4
    @10
    @2
    @7
    @4
    @10
    wi
    vg
    @2
    @4
    @7
    @10
    @2
    @4
    @7
    wa
    @3
    @6
    cG
    co
    #
    @9
    wcel
    #
    @10
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @3
    @6
    cF
    cG
    genp.1
    genp.2
    genpprecl
    @12
    @9
    c0
    wne
    @10
    @9
    @11
    ne0i
    @9
    0pss
    sylibr
    syl6
    expcomd
    exlimdv
    com23
    exlimdv
    impd
    mpd
end
