include "cr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "cmul.mm"
include "cmpt.mm"
include "cdv.mm"
include "cre.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cjcld.mm"
include "addcld.mm"
include "dvmptcl.mm"
include "dvmptcj.mm"
include "dvmptadd.mm"
include "halfcn.mm"
include "dvmptcmul.mm"
include "wceq.mm"
include "reval.mm"
include "syl.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divrec2.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem dvmptre
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
  assert |- ( ph -> ( RR _D ( x e. X |-> ( Re ` A ) ) ) = ( x e. X |-> ( Re ` B ) ) )

  proof
    wph
    cr
    vx
    cX
    c1
    c2
    cdiv
    co
    #
    cA
    cA
    ccj
    cfv
    #
    caddc
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
    @0
    cB
    cB
    ccj
    cfv
    #
    caddc
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
    cre
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    cre
    cfv
    #
    cmpt
    wph
    vx
    @2
    @6
    @0
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
    @1
    dvmptcj.a
    @12
    cA
    dvmptcj.a
    cjcld
    #
    addcld
    #
    @12
    cB
    @5
    wph
    vx
    cA
    cB
    cr
    cV
    cX
    @11
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    dvmptcl
    #
    @12
    cB
    @15
    cjcld
    #
    addcld
    #
    wph
    vx
    cA
    cB
    @1
    @5
    cr
    cV
    cc
    cX
    @11
    dvmptcj.a
    dvmptcj.b
    dvmptcj.da
    @13
    @16
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
    dvmptadd
    @0
    cc
    wcel
    wph
    halfcn
    a1i
    dvmptcmul
    wph
    @9
    @4
    cr
    cdv
    wph
    vx
    cX
    @8
    @3
    @12
    @8
    @2
    c2
    cdiv
    co
    #
    @3
    @12
    cA
    cc
    wcel
    @8
    @18
    wceq
    dvmptcj.a
    cA
    reval
    syl
    @12
    @2
    cc
    wcel
    #
    @18
    @3
    wceq
    #
    @14
    @19
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @20
    2cn
    2ne0
    @2
    c2
    divrec2
    mp3an23
    syl
    eqtrd
    mpteq2dva
    oveq2d
    wph
    vx
    cX
    @10
    @7
    @12
    @10
    @6
    c2
    cdiv
    co
    #
    @7
    @12
    cB
    cc
    wcel
    @10
    @23
    wceq
    @15
    cB
    reval
    syl
    @12
    @6
    cc
    wcel
    #
    @23
    @7
    wceq
    #
    @17
    @24
    @21
    @22
    @25
    2cn
    2ne0
    @6
    c2
    divrec2
    mp3an23
    syl
    eqtrd
    mpteq2dva
    3eqtr4d
end
