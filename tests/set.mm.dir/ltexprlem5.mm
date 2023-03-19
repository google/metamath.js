include "cnp.mm"
include "wcel.mm"
include "wpss.mm"
include "wa.mm"
include "c0.mm"
include "cnq.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "wne.mm"
include "ltexprlem1.mm"
include "0pss.mm"
include "syl6ibr.mm"
include "imp.mm"
include "ltexprlem2.mm"
include "adantr.mm"
include "ltexprlem3.mm"
include "wex.mm"
include "ltexprlem4.mm"
include "df-rex.mm"
include "jcad.mm"
include "ralrimiv.mm"
include "jca31.mm"
include "elnp.mm"
include "sylibr.mm"

theorem ltexprlem5
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
  assert |- ( ( B e. P. /\ A C. B ) -> C e. P. )

  proof
    cB
    cnp
    wcel
    #
    cA
    cB
    wpss
    #
    wa
    #
    c0
    cC
    wpss
    #
    cC
    cnq
    wpss
    #
    wa
    vz
    cv
    #
    vx
    cv
    #
    cltq
    wbr
    @5
    cC
    wcel
    #
    wi
    vz
    wal
    #
    @6
    @5
    cltq
    wbr
    #
    vz
    cC
    wrex
    #
    wa
    #
    vx
    cC
    wral
    #
    wa
    cC
    cnp
    wcel
    @2
    @3
    @4
    @12
    @0
    @1
    @3
    @0
    @1
    cC
    c0
    wne
    @3
    vx
    vy
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem1
    cC
    0pss
    syl6ibr
    imp
    @0
    @4
    @1
    vx
    vy
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem2
    adantr
    @0
    @12
    @1
    @0
    @11
    vx
    cC
    @0
    @6
    cC
    wcel
    #
    @8
    @10
    vx
    vy
    vz
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem3
    @0
    @13
    @7
    @9
    wa
    vz
    wex
    @10
    vx
    vy
    vz
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem4
    @9
    vz
    cC
    df-rex
    syl6ibr
    jcad
    ralrimiv
    adantr
    jca31
    vx
    vz
    cC
    elnp
    sylibr
end
