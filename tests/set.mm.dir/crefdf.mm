include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "ccref.mm"
include "eleq2i.mm"
include "crefi.mm"
include "syl3an1b.mm"
include "elin.mm"
include "anim2i.mm"
include "sylbi.mm"
include "anim1i.mm"
include "anass.mm"
include "sylib.mm"
include "reximi2.mm"
include "syl.mm"

theorem crefdf
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cX: class X
  let vy: setvar y
  assume crefi.x: |- X = U. J
  assume crefdf.b: |- B = CovHasRef A
  assume crefdf.p: |- ( z e. A -> ph )

  disjoint A z
  disjoint J z
  disjoint C z
  disjoint A y
  disjoint y z
  disjoint J y
  disjoint C y
  disjoint X y
  assert |- ( ( J e. B /\ C C_ J /\ X = U. C ) -> E. z e. ~P J ( ph /\ z Ref C ) )

  proof
    cJ
    cB
    wcel
    #
    cC
    cJ
    wss
    #
    cX
    cC
    cuni
    wceq
    #
    w3a
    vz
    cv
    #
    cC
    cref
    wbr
    #
    vz
    cJ
    cpw
    #
    cA
    cin
    #
    wrex
    #
    wph
    @4
    wa
    #
    vz
    @5
    wrex
    @0
    cJ
    cA
    ccref
    #
    wcel
    @1
    @2
    @7
    cB
    @9
    cJ
    crefdf.b
    eleq2i
    vz
    cA
    cC
    cJ
    cX
    crefi.x
    crefi
    syl3an1b
    @4
    @8
    vz
    @6
    @5
    @3
    @6
    wcel
    #
    @4
    wa
    @3
    @5
    wcel
    #
    wph
    wa
    #
    @4
    wa
    @11
    @8
    wa
    @10
    @12
    @4
    @10
    @11
    @3
    cA
    wcel
    #
    wa
    @12
    @3
    @5
    cA
    elin
    @13
    wph
    @11
    crefdf.p
    anim2i
    sylbi
    anim1i
    @11
    wph
    @4
    anass
    sylib
    reximi2
    syl
end
