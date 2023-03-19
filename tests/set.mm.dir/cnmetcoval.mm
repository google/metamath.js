include "ccom.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cc.mm"
include "fvovco.mm"
include "wcel.mm"
include "wceq.mm"
include "cxp.mm"
include "ffvelrnd.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cnmetcoval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  assume cnmetcoval.d: |- D = ( abs o. - )
  assume cnmetcoval.f: |- ( ph -> F : A --> ( CC X. CC ) )
  assume cnmetcoval.b: |- ( ph -> B e. A )


  assert |- ( ph -> ( ( D o. F ) ` B ) = ( abs ` ( ( 1st ` ( F ` B ) ) - ( 2nd ` ( F ` B ) ) ) ) )

  proof
    wph
    cB
    cD
    cF
    ccom
    cfv
    cB
    cF
    cfv
    #
    c1st
    cfv
    #
    @0
    c2nd
    cfv
    #
    cD
    co
    #
    @1
    @2
    cmin
    co
    cabs
    cfv
    #
    wph
    cF
    cD
    cc
    cc
    cA
    cB
    cnmetcoval.f
    cnmetcoval.b
    fvovco
    wph
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @3
    @4
    wceq
    wph
    @0
    cc
    cc
    cxp
    #
    wcel
    #
    @5
    wph
    cA
    @7
    cB
    cF
    cnmetcoval.f
    cnmetcoval.b
    ffvelrnd
    #
    @0
    cc
    cc
    xp1st
    syl
    wph
    @8
    @6
    @9
    @0
    cc
    cc
    xp2nd
    syl
    @1
    @2
    cD
    cnmetcoval.d
    cnmetdval
    syl2anc
    eqtrd
end
