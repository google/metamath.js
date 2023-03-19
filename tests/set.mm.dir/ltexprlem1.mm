include "cnp.mm"
include "wcel.mm"
include "wpss.mm"
include "cv.mm"
include "wn.mm"
include "cplq.mm"
include "co.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "pssnel.mm"
include "prnmadd.mm"
include "anim2i.mm"
include "19.42v.mm"
include "sylibr.mm"
include "exp32.mm"
include "com3l.mm"
include "impd.mm"
include "eximdv.mm"
include "syl5.mm"
include "abeq2i.mm"
include "exbii.mm"
include "n0.mm"
include "excom.mm"
include "3bitr4i.mm"
include "syl6ibr.mm"

theorem ltexprlem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume ltexprlem.1: |- C = { x | E. y ( -. y e. A /\ ( y +Q x ) e. B ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint v w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint A w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint A v
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  disjoint f u
  disjoint g u
  disjoint h u
  assert |- ( B e. P. -> ( A C. B -> C =/= (/) ) )

  proof
    cB
    cnp
    wcel
    #
    cA
    cB
    wpss
    #
    vy
    cv
    #
    cA
    wcel
    wn
    #
    @2
    vx
    cv
    #
    cplq
    co
    cB
    wcel
    #
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    cC
    c0
    wne
    #
    @1
    @2
    cB
    wcel
    #
    @3
    wa
    #
    vy
    wex
    @0
    @8
    vy
    cA
    cB
    pssnel
    @0
    @11
    @7
    vy
    @0
    @10
    @3
    @7
    @3
    @0
    @10
    @7
    @3
    @0
    @10
    @7
    @3
    @0
    @10
    wa
    #
    wa
    @3
    @5
    vx
    wex
    #
    wa
    @7
    @12
    @13
    @3
    vx
    cB
    @2
    prnmadd
    anim2i
    @3
    @5
    vx
    19.42v
    sylibr
    exp32
    com3l
    impd
    eximdv
    syl5
    @4
    cC
    wcel
    #
    vx
    wex
    @6
    vy
    wex
    #
    vx
    wex
    @9
    @8
    @14
    @15
    vx
    @15
    vx
    cC
    ltexprlem.1
    abeq2i
    exbii
    vx
    cC
    n0
    @6
    vy
    vx
    excom
    3bitr4i
    syl6ibr
end
