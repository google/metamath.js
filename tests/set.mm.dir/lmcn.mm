include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "ccnp.mm"
include "cfv.mm"
include "ctopon.mm"
include "clm.mm"
include "wbr.mm"
include "ctop.mm"
include "cntop1.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "cncnpi.mm"
include "lmcnp.mm"

theorem lmcn
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  assume lmcnp.3: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmcn.4: |- ( ph -> G e. ( J Cn K ) )


  assert |- ( ph -> ( G o. F ) ( ~~>t ` K ) ( G ` P ) )

  proof
    wph
    cP
    cF
    cG
    cJ
    cK
    lmcnp.3
    wph
    cG
    cJ
    cK
    ccn
    co
    wcel
    #
    cP
    cJ
    cuni
    #
    wcel
    #
    cG
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    lmcn.4
    wph
    cJ
    @1
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    @2
    wph
    cJ
    ctop
    wcel
    #
    @3
    wph
    @0
    @4
    lmcn.4
    cG
    cJ
    cK
    cntop1
    syl
    cJ
    @1
    @1
    eqid
    #
    toptopon
    sylib
    lmcnp.3
    cP
    cF
    cJ
    @1
    lmcl
    syl2anc
    cP
    cG
    cJ
    cK
    @1
    @5
    cncnpi
    syl2anc
    lmcnp
end
