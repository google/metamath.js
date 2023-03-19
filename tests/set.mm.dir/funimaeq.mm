include "cima.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "funfnd.mm"
include "adantr.mm"
include "simpr.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimia.mm"
include "wfun.mm"
include "wb.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "eqssd.mm"

theorem funimaeq
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  assume funimaeq.x: |- F/ x ph
  assume funimaeq.f: |- ( ph -> Fun F )
  assume funimaeq.g: |- ( ph -> Fun G )
  assume funimaeq.a: |- ( ph -> A C_ dom F )
  assume funimaeq.d: |- ( ph -> A C_ dom G )
  assume funimaeq.e: |- ( ( ph /\ x e. A ) -> ( F ` x ) = ( G ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  assert |- ( ph -> ( F " A ) = ( G " A ) )

  proof
    wph
    cF
    cA
    cima
    #
    cG
    cA
    cima
    #
    wph
    @0
    @1
    wss
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    wph
    @5
    vx
    cA
    funimaeq.x
    wph
    @3
    cA
    wcel
    #
    wa
    #
    @4
    @3
    cG
    cfv
    #
    @1
    funimaeq.e
    @8
    cG
    cG
    cdm
    #
    wfn
    #
    cA
    @10
    wss
    #
    @7
    @9
    @1
    wcel
    wph
    @11
    @7
    wph
    cG
    funimaeq.g
    funfnd
    adantr
    wph
    @12
    @7
    funimaeq.d
    adantr
    wph
    @7
    simpr
    #
    @10
    cA
    cG
    @3
    fnfvima
    syl3anc
    eqeltrd
    ralrimia
    wph
    cF
    wfun
    cA
    cF
    cdm
    #
    wss
    #
    @2
    @6
    wb
    funimaeq.f
    funimaeq.a
    vx
    cA
    @1
    cF
    funimass4
    syl2anc
    mpbird
    wph
    @1
    @0
    wss
    #
    @9
    @0
    wcel
    #
    vx
    cA
    wral
    #
    wph
    @17
    vx
    cA
    funimaeq.x
    @8
    @9
    @4
    @0
    @8
    @4
    @9
    funimaeq.e
    eqcomd
    @8
    cF
    @14
    wfn
    #
    @15
    @7
    @4
    @0
    wcel
    wph
    @19
    @7
    wph
    cF
    funimaeq.f
    funfnd
    adantr
    wph
    @15
    @7
    funimaeq.a
    adantr
    @13
    @14
    cA
    cF
    @3
    fnfvima
    syl3anc
    eqeltrd
    ralrimia
    wph
    cG
    wfun
    @12
    @16
    @18
    wb
    funimaeq.g
    funimaeq.d
    vx
    cA
    @0
    cG
    funimass4
    syl2anc
    mpbird
    eqssd
end
