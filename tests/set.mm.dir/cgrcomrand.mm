include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "wb.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cgrcomr.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpbid.mm"

theorem cgrcomrand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  assume cgrcomlrand.1: |- ( ph -> N e. NN )
  assume cgrcomlrand.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrcomlrand.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrcomlrand.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrcomlrand.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrcomlrand.6: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )


  assert |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. D , C >. )

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
    ccgr
    wbr
    #
    @0
    cD
    cC
    cop
    ccgr
    wbr
    #
    cgrcomlrand.6
    wph
    @1
    @2
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
    @4
    wcel
    cC
    @4
    wcel
    cD
    @4
    wcel
    @3
    cgrcomlrand.1
    cgrcomlrand.2
    cgrcomlrand.3
    cgrcomlrand.4
    cgrcomlrand.5
    cA
    cB
    cC
    cD
    cN
    cgrcomr
    syl122anc
    adantr
    mpbid
end
