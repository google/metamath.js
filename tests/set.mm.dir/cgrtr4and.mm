include "wa.mm"
include "cn.mm"
include "wcel.mm"
include "adantr.mm"
include "cee.mm"
include "cfv.mm"
include "cgrtr4d.mm"

theorem cgrtr4and
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  assume cgrtr4and.1: |- ( ph -> N e. NN )
  assume cgrtr4and.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrtr4and.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrtr4and.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrtr4and.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrtr4and.6: |- ( ph -> E e. ( EE ` N ) )
  assume cgrtr4and.7: |- ( ph -> F e. ( EE ` N ) )
  assume cgrtr4and.8: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )
  assume cgrtr4and.9: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. )


  assert |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. )

  proof
    wph
    wps
    wa
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    wph
    cN
    cn
    wcel
    wps
    cgrtr4and.1
    adantr
    wph
    cA
    cN
    cee
    cfv
    #
    wcel
    wps
    cgrtr4and.2
    adantr
    wph
    cB
    @0
    wcel
    wps
    cgrtr4and.3
    adantr
    wph
    cC
    @0
    wcel
    wps
    cgrtr4and.4
    adantr
    wph
    cD
    @0
    wcel
    wps
    cgrtr4and.5
    adantr
    wph
    cE
    @0
    wcel
    wps
    cgrtr4and.6
    adantr
    wph
    cF
    @0
    wcel
    wps
    cgrtr4and.7
    adantr
    cgrtr4and.8
    cgrtr4and.9
    cgrtr4d
end
