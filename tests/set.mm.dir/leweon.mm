include "con0.mm"
include "cep.mm"
include "wwe.mm"
include "cxp.mm"
include "epweon.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "c2nd.mm"
include "wo.mm"
include "copab.mm"
include "wbr.mm"
include "fvex.mm"
include "epelc.mm"
include "anbi2i.mm"
include "orbi12i.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "wexp.mm"
include "mp2an.mm"

theorem leweon
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cA: class A
  let va: setvar a
  let cJ: class J
  let vw: setvar w
  let vu: setvar u
  let vz: setvar z
  let vm: setvar m
  let cM: class M
  let wph: wff ph
  let cQ: class Q
  let cR: class R
  assume leweon.1: |- L = { <. x , y >. | ( ( x e. ( On X. On ) /\ y e. ( On X. On ) ) /\ ( ( 1st ` x ) e. ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) e. ( 2nd ` y ) ) ) ) }

  disjoint x y
  disjoint A a
  disjoint J w
  disjoint u w
  disjoint u z
  disjoint L u
  disjoint w z
  disjoint L w
  disjoint L z
  disjoint m z
  disjoint M m
  disjoint M z
  disjoint ph w
  disjoint ph z
  disjoint Q z
  disjoint a m
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint u x
  disjoint u y
  disjoint w x
  disjoint w y
  disjoint x z
  disjoint y z
  disjoint R u
  assert |- L We ( On X. On )

  proof
    con0
    cep
    wwe
    #
    @0
    con0
    con0
    cxp
    #
    cL
    wwe
    epweon
    epweon
    vx
    vy
    con0
    con0
    cep
    cep
    cL
    cL
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @1
    wcel
    wa
    #
    @2
    c1st
    cfv
    #
    @3
    c1st
    cfv
    #
    wcel
    #
    @5
    @6
    wceq
    #
    @2
    c2nd
    cfv
    #
    @3
    c2nd
    cfv
    #
    wcel
    #
    wa
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    @4
    @5
    @6
    cep
    wbr
    #
    @8
    @9
    @10
    cep
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    vx
    vy
    copab
    leweon.1
    @19
    @14
    vx
    vy
    @18
    @13
    @4
    @15
    @7
    @17
    @12
    @5
    @6
    @3
    c1st
    fvex
    epelc
    @16
    @11
    @8
    @9
    @10
    @3
    c2nd
    fvex
    epelc
    anbi2i
    orbi12i
    anbi2i
    opabbii
    eqtr4i
    wexp
    mp2an
end
