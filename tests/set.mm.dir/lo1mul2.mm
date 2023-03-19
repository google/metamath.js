include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "clo1.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "lo1mptrcl.mm"
include "recnd.mm"
include "mulcomd.mm"
include "mpteq2dva.mm"
include "lo1mul.mm"
include "eqeltrd.mm"

theorem lo1mul2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume o1add2.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1add2.2: |- ( ( ph /\ x e. A ) -> C e. V )
  assume lo1add.3: |- ( ph -> ( x e. A |-> B ) e. <_O(1) )
  assume lo1add.4: |- ( ph -> ( x e. A |-> C ) e. <_O(1) )
  assume lo1mul.5: |- ( ( ph /\ x e. A ) -> 0 <_ B )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint C c
  disjoint C m
  disjoint C n
  disjoint C p
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( x e. A |-> ( C x. B ) ) e. <_O(1) )

  proof
    wph
    vx
    cA
    cC
    cB
    cmul
    co
    #
    cmpt
    vx
    cA
    cB
    cC
    cmul
    co
    #
    cmpt
    clo1
    wph
    vx
    cA
    @0
    @1
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    cB
    @2
    cC
    wph
    vx
    cA
    cC
    cV
    o1add2.2
    lo1add.4
    lo1mptrcl
    recnd
    @2
    cB
    wph
    vx
    cA
    cB
    cV
    o1add2.1
    lo1add.3
    lo1mptrcl
    recnd
    mulcomd
    mpteq2dva
    wph
    vx
    cA
    cB
    cC
    cV
    o1add2.1
    o1add2.2
    lo1add.3
    lo1add.4
    lo1mul.5
    lo1mul
    eqeltrd
end
