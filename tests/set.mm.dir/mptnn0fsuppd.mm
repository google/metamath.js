include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "csb.mm"
include "vex.mm"
include "csbie.mm"
include "id.mm"
include "syl5eq.mm"
include "imim2i.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl.mm"
include "mptnn0fsupp.mm"

theorem mptnn0fsuppd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let c.0: class .0.
  let vs: setvar s
  assume mptnn0fsupp.0: |- ( ph -> .0. e. V )
  assume mptnn0fsupp.c: |- ( ( ph /\ k e. NN0 ) -> C e. B )
  assume mptnn0fsuppd.d: |- ( k = x -> C = D )
  assume mptnn0fsuppd.s: |- ( ph -> E. s e. NN0 A. x e. NN0 ( s < x -> D = .0. ) )

  disjoint D k
  disjoint B k
  disjoint C s
  disjoint C x
  disjoint s x
  disjoint k ph
  disjoint ph s
  disjoint ph x
  disjoint k s
  disjoint k x
  disjoint .0. s
  disjoint .0. x
  assert |- ( ph -> ( k e. NN0 |-> C ) finSupp .0. )

  proof
    wph
    vx
    cB
    cC
    vk
    cV
    c.0
    vs
    mptnn0fsupp.0
    mptnn0fsupp.c
    wph
    vs
    cv
    vx
    cv
    #
    clt
    wbr
    #
    cD
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @1
    vk
    @0
    cC
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    mptnn0fsuppd.s
    @4
    @8
    vs
    cn0
    @3
    @7
    vx
    cn0
    @2
    @6
    @1
    @2
    @5
    cD
    c.0
    vk
    @0
    cC
    cD
    vx
    vex
    mptnn0fsuppd.d
    csbie
    @2
    id
    syl5eq
    imim2i
    ralimi
    reximi
    syl
    mptnn0fsupp
end
