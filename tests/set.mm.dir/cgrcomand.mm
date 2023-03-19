include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wb.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cgrcom.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpbid.mm"

theorem cgrcomand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  assume cgrcomand.1: |- ( ph -> N e. NN )
  assume cgrcomand.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrcomand.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrcomand.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrcomand.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrcomand.6: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )


  assert |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. A , B >. )

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
    @0
    ccgr
    wbr
    #
    cgrcomand.6
    wph
    @2
    @3
    wb
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
    @5
    wcel
    cC
    @5
    wcel
    cD
    @5
    wcel
    @4
    cgrcomand.1
    cgrcomand.2
    cgrcomand.3
    cgrcomand.4
    cgrcomand.5
    cA
    cB
    cC
    cD
    cN
    cgrcom
    syl122anc
    adantr
    mpbid
end
