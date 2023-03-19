include "wa.mm"
include "wne.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "ccgr.mm"
include "jca.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "linecgr.mm"
include "syl132anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem linecgrand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cN: class N
  assume linecgrand.1: |- ( ph -> N e. NN )
  assume linecgrand.2: |- ( ph -> A e. ( EE ` N ) )
  assume linecgrand.3: |- ( ph -> B e. ( EE ` N ) )
  assume linecgrand.4: |- ( ph -> C e. ( EE ` N ) )
  assume linecgrand.5: |- ( ph -> P e. ( EE ` N ) )
  assume linecgrand.6: |- ( ph -> Q e. ( EE ` N ) )
  assume linecgrand.7: |- ( ( ph /\ ps ) -> A =/= B )
  assume linecgrand.8: |- ( ( ph /\ ps ) -> A Colinear <. B , C >. )
  assume linecgrand.9: |- ( ( ph /\ ps ) -> <. A , P >. Cgr <. A , Q >. )
  assume linecgrand.10: |- ( ( ph /\ ps ) -> <. B , P >. Cgr <. B , Q >. )


  assert |- ( ( ph /\ ps ) -> <. C , P >. Cgr <. C , Q >. )

  proof
    wph
    wps
    wa
    #
    cA
    cB
    wne
    #
    cA
    cB
    cC
    cop
    ccolin
    wbr
    #
    wa
    #
    cA
    cP
    cop
    cA
    cQ
    cop
    ccgr
    wbr
    #
    cB
    cP
    cop
    cB
    cQ
    cop
    ccgr
    wbr
    #
    wa
    #
    cC
    cP
    cop
    cC
    cQ
    cop
    ccgr
    wbr
    #
    @0
    @1
    @2
    linecgrand.7
    linecgrand.8
    jca
    @0
    @4
    @5
    linecgrand.9
    linecgrand.10
    jca
    wph
    @3
    @6
    wa
    @7
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
    @9
    wcel
    cC
    @9
    wcel
    cP
    @9
    wcel
    cQ
    @9
    wcel
    @8
    linecgrand.1
    linecgrand.2
    linecgrand.3
    linecgrand.4
    linecgrand.5
    linecgrand.6
    cA
    cB
    cC
    cP
    cQ
    cN
    linecgr
    syl132anc
    adantr
    mp2and
end
