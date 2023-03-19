include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cgrtr.mm"
include "syl133anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem cgrtrand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  assume cgrtrand.1: |- ( ph -> N e. NN )
  assume cgrtrand.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrtrand.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrtrand.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrtrand.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrtrand.6: |- ( ph -> E e. ( EE ` N ) )
  assume cgrtrand.7: |- ( ph -> F e. ( EE ` N ) )
  assume cgrtrand.8: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )
  assume cgrtrand.9: |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. )


  assert |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. )

  proof
    wph
    wps
    wa
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
    @1
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    @0
    @3
    ccgr
    wbr
    #
    cgrtrand.8
    cgrtrand.9
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
    cgrtrand.1
    cgrtrand.2
    cgrtrand.3
    cgrtrand.4
    cgrtrand.5
    cgrtrand.6
    cgrtrand.7
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    cgrtr
    syl133anc
    adantr
    mp2and
end
