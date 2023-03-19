include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "cv.mm"
include "simplr.mm"
include "simpr.mm"
include "cle.mm"
include "wbr.mm"
include "leid.mm"
include "ad2antlr.mm"
include "ello1d.mm"

theorem lo1const
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G a
  disjoint G b
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ( A C_ RR /\ B e. RR ) -> ( x e. A |-> B ) e. <_O(1) )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wcel
    #
    wa
    vx
    cA
    cB
    cB
    cB
    @0
    @1
    simpl
    @0
    @1
    vx
    cv
    #
    cA
    wcel
    #
    simplr
    @0
    @1
    simpr
    #
    @4
    @1
    cB
    cB
    cle
    wbr
    @0
    @3
    cB
    @2
    cle
    wbr
    wa
    cB
    leid
    ad2antlr
    ello1d
end
