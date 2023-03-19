include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "wi.mm"
include "axcgrtr.mm"
include "syl133anc.mm"
include "mp2and.mm"

theorem cgrtr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  assume cgrtr4d.1: |- ( ph -> N e. NN )
  assume cgrtr4d.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrtr4d.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrtr4d.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrtr4d.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrtr4d.6: |- ( ph -> E e. ( EE ` N ) )
  assume cgrtr4d.7: |- ( ph -> F e. ( EE ` N ) )
  assume cgrtr4d.8: |- ( ph -> <. A , B >. Cgr <. C , D >. )
  assume cgrtr4d.9: |- ( ph -> <. A , B >. Cgr <. E , F >. )


  assert |- ( ph -> <. C , D >. Cgr <. E , F >. )

  proof
    wph
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    @0
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    @1
    @3
    ccgr
    wbr
    #
    cgrtr4d.8
    cgrtr4d.9
    wph
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @6
    wcel
    cC
    @6
    wcel
    cD
    @6
    wcel
    cE
    @6
    wcel
    cF
    @6
    wcel
    @2
    @4
    wa
    @5
    wi
    cgrtr4d.1
    cgrtr4d.2
    cgrtr4d.3
    cgrtr4d.4
    cgrtr4d.5
    cgrtr4d.6
    cgrtr4d.7
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    axcgrtr
    syl133anc
    mp2and
end
