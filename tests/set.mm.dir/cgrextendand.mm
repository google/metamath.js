include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "jca.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cgrextend.mm"
include "syl133anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem cgrextendand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  assume cgrextendand.1: |- ( ph -> N e. NN )
  assume cgrextendand.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrextendand.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrextendand.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrextendand.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrextendand.6: |- ( ph -> E e. ( EE ` N ) )
  assume cgrextendand.7: |- ( ph -> F e. ( EE ` N ) )
  assume cgrextendand.8: |- ( ( ph /\ ps ) -> B Btwn <. A , C >. )
  assume cgrextendand.9: |- ( ( ph /\ ps ) -> E Btwn <. D , F >. )
  assume cgrextendand.10: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. D , E >. )
  assume cgrextendand.11: |- ( ( ph /\ ps ) -> <. B , C >. Cgr <. E , F >. )


  assert |- ( ( ph /\ ps ) -> <. A , C >. Cgr <. D , F >. )

  proof
    wph
    wps
    wa
    #
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cE
    cD
    cF
    cop
    #
    cbtwn
    wbr
    #
    wa
    #
    cA
    cB
    cop
    cD
    cE
    cop
    ccgr
    wbr
    #
    cB
    cC
    cop
    cE
    cF
    cop
    ccgr
    wbr
    #
    wa
    #
    @1
    @3
    ccgr
    wbr
    #
    @0
    @2
    @4
    cgrextendand.8
    cgrextendand.9
    jca
    @0
    @6
    @7
    cgrextendand.10
    cgrextendand.11
    jca
    wph
    @5
    @8
    wa
    @9
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
    @11
    wcel
    cC
    @11
    wcel
    cD
    @11
    wcel
    cE
    @11
    wcel
    cF
    @11
    wcel
    @10
    cgrextendand.1
    cgrextendand.2
    cgrextendand.3
    cgrextendand.4
    cgrextendand.5
    cgrextendand.6
    cgrextendand.7
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgrextend
    syl133anc
    adantr
    mp2and
end
