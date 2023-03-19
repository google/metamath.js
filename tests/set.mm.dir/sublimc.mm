include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "climc.mm"
include "cmin.mm"
include "eqid.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "negcld.mm"
include "neglimc.mm"
include "addlimc.mm"
include "cc.mm"
include "limccl.mm"
include "sseldi.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eltr4d.mm"

theorem sublimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  assume sublimc.f: |- F = ( x e. A |-> B )
  assume sublimc.2: |- G = ( x e. A |-> C )
  assume sublimc.3: |- H = ( x e. A |-> ( B - C ) )
  assume sublimc.4: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume sublimc.5: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume sublimc.6: |- ( ph -> E e. ( F limCC D ) )
  assume sublimc.7: |- ( ph -> I e. ( G limCC D ) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( E - I ) e. ( H limCC D ) )

  proof
    wph
    cE
    cI
    cneg
    #
    caddc
    co
    #
    vx
    cA
    cB
    cC
    cneg
    #
    caddc
    co
    #
    cmpt
    #
    cD
    climc
    co
    cE
    cI
    cmin
    co
    #
    cH
    cD
    climc
    co
    wph
    vx
    cA
    cB
    @2
    cD
    cE
    cF
    vx
    cA
    @2
    cmpt
    #
    @4
    @0
    sublimc.f
    @6
    eqid
    #
    @4
    eqid
    sublimc.4
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cC
    sublimc.5
    negcld
    sublimc.6
    wph
    vx
    cA
    cC
    cI
    cD
    cG
    @6
    sublimc.2
    @7
    sublimc.5
    sublimc.7
    neglimc
    addlimc
    wph
    @1
    @5
    wph
    cE
    cI
    wph
    cF
    cD
    climc
    co
    cc
    cE
    cD
    cF
    limccl
    sublimc.6
    sseldi
    wph
    cG
    cD
    climc
    co
    cc
    cI
    cD
    cG
    limccl
    sublimc.7
    sseldi
    negsubd
    eqcomd
    wph
    cH
    @4
    cD
    climc
    wph
    cH
    vx
    cA
    cB
    cC
    cmin
    co
    #
    cmpt
    @4
    sublimc.3
    wph
    vx
    cA
    @9
    @3
    @8
    @3
    @9
    @8
    cB
    cC
    sublimc.4
    sublimc.5
    negsubd
    eqcomd
    mpteq2dva
    syl5eq
    oveq1d
    3eltr4d
end
