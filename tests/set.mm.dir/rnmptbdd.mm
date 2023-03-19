include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "rnmptbddlem.mm"
include "wb.mm"
include "breq1.mm"
include "cbvralv.mm"
include "a1i.mm"
include "bitrd.mm"

theorem rnmptbdd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  assume rnmptbdd.x: |- F/ x ph
  assume rnmptbdd.b: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint A v
  disjoint A w
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint B v
  disjoint B w
  disjoint ph v
  disjoint ph w
  disjoint v x
  disjoint w x
  assert |- ( ph -> E. y e. RR A. z e. ran ( x e. A |-> B ) z <_ y )

  proof
    wph
    vw
    cv
    #
    vv
    cv
    #
    cle
    wbr
    #
    vw
    vx
    cA
    cB
    cmpt
    crn
    #
    wral
    #
    vv
    cr
    wrex
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    @3
    wral
    #
    vy
    cr
    wrex
    wph
    vx
    vv
    vw
    cA
    cB
    rnmptbdd.x
    wph
    cB
    @6
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    cB
    @1
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vv
    cr
    wrex
    rnmptbdd.b
    @10
    @12
    vy
    vv
    cr
    @6
    @1
    wceq
    @9
    @11
    vx
    cA
    @6
    @1
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    sylib
    rnmptbddlem
    @4
    @8
    vv
    vy
    cr
    @1
    @6
    wceq
    #
    @4
    @0
    @6
    cle
    wbr
    #
    vw
    @3
    wral
    #
    @8
    @13
    @2
    @14
    vw
    @3
    @1
    @6
    @0
    cle
    breq2
    ralbidv
    @15
    @8
    wb
    @13
    @14
    @7
    vw
    vz
    @3
    @0
    @5
    @6
    cle
    breq1
    cbvralv
    a1i
    bitrd
    cbvrexv
    sylib
end
