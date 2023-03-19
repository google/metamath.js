include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cgrtr3.mm"
include "syl133anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem cgrtr3and
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  assume cgrtr3and.1: |- ( ph -> N e. NN )
  assume cgrtr3and.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrtr3and.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrtr3and.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrtr3and.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrtr3and.6: |- ( ph -> E e. ( EE ` N ) )
  assume cgrtr3and.7: |- ( ph -> F e. ( EE ` N ) )
  assume cgrtr3and.8: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. )
  assume cgrtr3and.9: |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. )


  assert |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )

  proof
    wph
    wps
    wa
    cA
    cB
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    cC
    cD
    cop
    #
    @1
    ccgr
    wbr
    #
    @0
    @3
    ccgr
    wbr
    #
    cgrtr3and.8
    cgrtr3and.9
    wph
    @2
    @4
    wa
    @5
    wi
    #
    wps
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
    @7
    wcel
    cC
    @7
    wcel
    cD
    @7
    wcel
    cE
    @7
    wcel
    cF
    @7
    wcel
    @6
    cgrtr3and.1
    cgrtr3and.2
    cgrtr3and.3
    cgrtr3and.4
    cgrtr3and.5
    cgrtr3and.6
    cgrtr3and.7
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgrtr3
    syl133anc
    adantr
    mp2and
end
