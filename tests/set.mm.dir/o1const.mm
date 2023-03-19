include "cr.mm"
include "wss.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "co1.mm"
include "rlimconst.mm"
include "rlimo1.mm"
include "syl.mm"

theorem o1const
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
  assert |- ( ( A C_ RR /\ B e. CC ) -> ( x e. A |-> B ) e. O(1) )

  proof
    cA
    cr
    wss
    cB
    cc
    wcel
    wa
    vx
    cA
    cB
    cmpt
    #
    cB
    crli
    wbr
    @0
    co1
    wcel
    vx
    cA
    cB
    rlimconst
    cB
    @0
    rlimo1
    syl
end
