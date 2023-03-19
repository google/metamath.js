include "cr.mm"
include "c1.mm"
include "c2.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "ccj.mm"
include "cfv.mm"
include "cmin.mm"
include "cmpt.mm"
include "cdv.mm"
include "cim.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cjcld.mm"
include "subcld.mm"
include "dvmptcl.mm"
include "dvmptcj.mm"
include "dvmptsub.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "reccli.mm"
include "dvmptcmul.mm"
include "wceq.mm"
include "imval2.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem dvmptim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let vy: setvar y
  assume dvmptcj.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptcj.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptcj.da: |- ( ph -> ( RR _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )

  disjoint ph x
  disjoint V x
  disjoint X x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ph -> ( RR _D ( x e. X |-> ( Im ` A ) ) ) = ( x e. X |-> ( Im ` B ) ) )

  proof
    wph
    cr
    vx
    cX
    c1
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    cA
    cA
    ccj
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    @1
    cB
    cB
    ccj
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cmpt
    cr
    vx
    cX
    cA
    cim
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cim
    cfv
    #
    cmpt
    wph
    vx
    @3
    @7
    @1
    cr
    cc
    cX
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cA
    @2
    dvmptcj.a
    @13
    cA
    dvmptcj.a
    cjcld
    #
    subcld
    #
    @13
    cB
    @6
    wph
    vx
    cA
    cB
    cr
    cV
    cX
    @12
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    dvmptcl
    #
    @13
    cB
    @16
    cjcld
    #
    subcld
    #
    wph
    vx
    cA
    cB
    @2
    @6
    cr
    cV
    cc
    cX
    @12
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    @14
    @17
    wph
    vx
    cA
    cB
    cV
    cX
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    dvmptcj
    dvmptsub
    @1
    cc
    wcel
    wph
    @0
    2mulicn
    2muline0
    reccli
    a1i
    dvmptcmul
    wph
    @10
    @5
    cr
    cdv
    wph
    vx
    cX
    @9
    @4
    @13
    @9
    @3
    @0
    cdiv
    co
    #
    @4
    @13
    cA
    cc
    wcel
    @9
    @19
    wceq
    dvmptcj.a
    cA
    imval2
    syl
    @13
    @3
    cc
    wcel
    #
    @19
    @4
    wceq
    #
    @15
    @20
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    @21
    2mulicn
    2muline0
    @3
    @0
    divrec2
    mp3an23
    syl
    eqtrd
    mpteq2dva
    oveq2d
    wph
    vx
    cX
    @11
    @8
    @13
    @11
    @7
    @0
    cdiv
    co
    #
    @8
    @13
    cB
    cc
    wcel
    @11
    @24
    wceq
    @16
    cB
    imval2
    syl
    @13
    @7
    cc
    wcel
    #
    @24
    @8
    wceq
    #
    @18
    @25
    @22
    @23
    @26
    2mulicn
    2muline0
    @7
    @0
    divrec2
    mp3an23
    syl
    eqtrd
    mpteq2dva
    3eqtr4d
end
