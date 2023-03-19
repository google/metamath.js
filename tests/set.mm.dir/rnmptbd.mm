include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "nfv.mm"
include "rnmptbdlem.mm"
include "breq1.mm"
include "cbvralv.mm"
include "bitrd.mm"
include "3bitrd.mm"

theorem rnmptbd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cV: class V
  let vu: setvar u
  let vw: setvar w
  assume rnmptbd.x: |- F/ x ph
  assume rnmptbd.b: |- ( ( ph /\ x e. A ) -> B e. V )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint A u
  disjoint A w
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint w y
  disjoint w z
  disjoint B u
  disjoint B w
  disjoint ph w
  disjoint u x
  disjoint w x
  assert |- ( ph -> ( E. y e. RR A. x e. A B <_ y <-> E. y e. RR A. z e. ran ( x e. A |-> B ) z <_ y ) )

  proof
    wph
    cB
    vy
    cv
    #
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
    #
    cB
    vw
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vw
    cr
    wrex
    #
    vu
    cv
    #
    @4
    cle
    wbr
    #
    vu
    vx
    cA
    cB
    cmpt
    crn
    #
    wral
    #
    vw
    cr
    wrex
    #
    vz
    cv
    #
    @0
    cle
    wbr
    #
    vz
    @10
    wral
    #
    vy
    cr
    wrex
    #
    @3
    @7
    wb
    wph
    @2
    @6
    vy
    vw
    cr
    @0
    @4
    wceq
    @1
    @5
    vx
    cA
    @0
    @4
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    a1i
    wph
    vx
    vw
    vu
    cA
    cB
    cV
    rnmptbd.x
    wph
    vw
    nfv
    rnmptbd.b
    rnmptbdlem
    @12
    @16
    wb
    wph
    @11
    @15
    vw
    vy
    cr
    @4
    @0
    wceq
    #
    @11
    @8
    @0
    cle
    wbr
    #
    vu
    @10
    wral
    #
    @15
    @17
    @9
    @18
    vu
    @10
    @4
    @0
    @8
    cle
    breq2
    ralbidv
    @19
    @15
    wb
    @17
    @18
    @14
    vu
    vz
    @10
    @8
    @13
    @0
    cle
    breq1
    cbvralv
    a1i
    bitrd
    cbvrexv
    a1i
    3bitrd
end
