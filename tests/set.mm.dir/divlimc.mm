include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmpt.mm"
include "climc.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "eldifad.mm"
include "reccld.mm"
include "reclimc.mm"
include "mullimc.mm"
include "limccl.mm"
include "sseldi.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eltr4d.mm"

theorem divlimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  assume divlimc.f: |- F = ( x e. A |-> B )
  assume divlimc.g: |- G = ( x e. A |-> C )
  assume divlimc.h: |- H = ( x e. A |-> ( B / C ) )
  assume divlimc.b: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume divlimc.c: |- ( ( ph /\ x e. A ) -> C e. ( CC \ { 0 } ) )
  assume divlimc.x: |- ( ph -> X e. ( F limCC D ) )
  assume divlimc.y: |- ( ph -> Y e. ( G limCC D ) )
  assume divlimc.yne0: |- ( ph -> Y =/= 0 )
  assume divlimc.cne0: |- ( ( ph /\ x e. A ) -> C =/= 0 )

  disjoint A x
  disjoint D x
  disjoint X x
  disjoint Y x
  disjoint ph x
  assert |- ( ph -> ( X / Y ) e. ( H limCC D ) )

  proof
    wph
    cX
    c1
    cY
    cdiv
    co
    #
    cmul
    co
    vx
    cA
    cB
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cD
    climc
    co
    cX
    cY
    cdiv
    co
    cH
    cD
    climc
    co
    wph
    vx
    cA
    cB
    @1
    cD
    cF
    vx
    cA
    @1
    cmpt
    #
    @3
    cX
    @0
    divlimc.f
    @4
    eqid
    #
    @3
    eqid
    divlimc.b
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    @6
    cC
    cc
    cc0
    csn
    divlimc.c
    eldifad
    #
    divlimc.cne0
    reccld
    divlimc.x
    wph
    vx
    cA
    cC
    cY
    cD
    cG
    @4
    divlimc.g
    @5
    divlimc.c
    divlimc.y
    divlimc.yne0
    reclimc
    mullimc
    wph
    cX
    cY
    wph
    cF
    cD
    climc
    co
    cc
    cX
    cD
    cF
    limccl
    divlimc.x
    sseldi
    wph
    cG
    cD
    climc
    co
    cc
    cY
    cD
    cG
    limccl
    divlimc.y
    sseldi
    divlimc.yne0
    divrecd
    wph
    cH
    @3
    cD
    climc
    wph
    cH
    vx
    cA
    cB
    cC
    cdiv
    co
    #
    cmpt
    @3
    divlimc.h
    wph
    vx
    cA
    @8
    @2
    @6
    cB
    cC
    divlimc.b
    @7
    divlimc.cne0
    divrecd
    mpteq2dva
    syl5eq
    oveq1d
    3eltr4d
end
