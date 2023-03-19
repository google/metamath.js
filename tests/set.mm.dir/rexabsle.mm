include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "nfv.mm"
include "breq2.mm"
include "ralbid.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "rexabslelem.mm"
include "ralbidv.mm"
include "breq1.mm"
include "anbi12i.mm"
include "3bitrd.mm"

theorem rexabsle
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume rexabsle.1: |- F/ x ph
  assume rexabsle.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A w
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint x y
  disjoint x z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint b w
  disjoint a y
  disjoint c z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint a x
  disjoint b x
  disjoint c x
  assert |- ( ph -> ( E. y e. RR A. x e. A ( abs ` B ) <_ y <-> ( E. w e. RR A. x e. A B <_ w /\ E. z e. RR A. x e. A z <_ B ) ) )

  proof
    wph
    cB
    cabs
    cfv
    #
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
    @0
    va
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    va
    cr
    wrex
    #
    cB
    vb
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vb
    cr
    wrex
    #
    vc
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vc
    cr
    wrex
    #
    wa
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
    vz
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    wa
    #
    @4
    @8
    wb
    wph
    @3
    @7
    vy
    va
    cr
    @1
    @5
    wceq
    #
    @2
    @6
    vx
    cA
    @27
    vx
    nfv
    @1
    @5
    @0
    cle
    breq2
    ralbid
    cbvrexv
    a1i
    wph
    vx
    va
    vc
    vb
    cA
    cB
    rexabsle.1
    rexabsle.2
    rexabslelem
    @17
    @26
    wb
    wph
    @12
    @21
    @16
    @25
    @11
    @20
    vb
    vw
    cr
    @9
    @18
    wceq
    @10
    @19
    vx
    cA
    @9
    @18
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    @15
    @24
    vc
    vz
    cr
    @13
    @22
    wceq
    @14
    @23
    vx
    cA
    @13
    @22
    cB
    cle
    breq1
    ralbidv
    cbvrexv
    anbi12i
    a1i
    3bitrd
end
