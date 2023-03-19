include "cv.mm"
include "wceq.mm"
include "ciun.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wrex.mm"
include "eliun.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "wi.mm"
include "3exp.mm"
include "rexlimdvw.mm"
include "imp.mm"
include "syl5bi.mm"
include "con3d.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "disj.mm"
include "sylibr.mm"
include "ex.mm"
include "orrd.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "disjiunb.mm"

theorem disjiund
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume disjiund.1: |- ( a = c -> A = C )
  assume disjiund.2: |- ( b = d -> C = D )
  assume disjiund.3: |- ( a = c -> W = X )
  assume disjiund.4: |- ( ( ph /\ x e. A /\ x e. D ) -> a = c )

  disjoint A c
  disjoint A d
  disjoint A x
  disjoint c d
  disjoint c x
  disjoint d x
  disjoint C a
  disjoint C d
  disjoint C x
  disjoint a d
  disjoint a x
  disjoint D b
  disjoint V a
  disjoint V c
  disjoint a c
  disjoint W b
  disjoint W c
  disjoint W d
  disjoint W x
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint X a
  disjoint X b
  disjoint X d
  disjoint X x
  disjoint a b
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph x
  assert |- ( ph -> Disj_ a e. V U_ b e. W A )

  proof
    wph
    va
    cv
    #
    vc
    cv
    #
    wceq
    #
    vb
    cW
    cA
    ciun
    #
    vb
    cX
    cC
    ciun
    #
    cin
    c0
    wceq
    #
    wo
    #
    vc
    cV
    wral
    va
    cV
    wral
    va
    cV
    @3
    wdisj
    wph
    @6
    va
    vc
    cV
    cV
    wph
    @6
    @0
    cV
    wcel
    @1
    cV
    wcel
    wa
    wph
    @2
    @5
    wph
    @2
    wn
    #
    @5
    wph
    @7
    wa
    #
    vx
    cv
    #
    @4
    wcel
    #
    wn
    #
    vx
    @3
    wral
    @5
    @8
    @11
    vx
    @3
    @9
    @3
    wcel
    @9
    cA
    wcel
    #
    vb
    cW
    wrex
    #
    @8
    @11
    vb
    @9
    cW
    cA
    eliun
    wph
    @13
    @7
    @11
    wph
    @13
    wa
    #
    @10
    @2
    @10
    @9
    cC
    wcel
    #
    vb
    cX
    wrex
    #
    @14
    @2
    vb
    @9
    cX
    cC
    eliun
    @16
    @9
    cD
    wcel
    #
    vd
    cX
    wrex
    @14
    @2
    @15
    @17
    vb
    vd
    cX
    vb
    cv
    vd
    cv
    wceq
    cC
    cD
    @9
    disjiund.2
    eleq2d
    cbvrexv
    @14
    @17
    @2
    vd
    cX
    wph
    @13
    @17
    @2
    wi
    #
    wph
    @12
    @18
    vb
    cW
    wph
    @12
    @17
    @2
    disjiund.4
    3exp
    rexlimdvw
    imp
    rexlimdvw
    syl5bi
    syl5bi
    con3d
    impancom
    syl5bi
    ralrimiv
    vx
    @3
    @4
    disj
    sylibr
    ex
    orrd
    a1d
    ralrimivv
    vb
    cV
    cW
    cA
    cX
    va
    vc
    cC
    disjiund.3
    disjiund.1
    disjiunb
    sylibr
end
