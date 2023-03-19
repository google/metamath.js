include "ccnv.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "crest.mm"
include "cmpt.mm"
include "cr.mm"
include "smff.mm"
include "feqmptd.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "wceq.mm"
include "eqid.mm"
include "mptpreima.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cvv.mm"
include "nfv.mm"
include "cuni.mm"
include "csalg.mm"
include "uniexd.mm"
include "smfdmss.mm"
include "ssexd.mm"
include "ffvelrnda.mm"
include "csmblfn.mm"
include "eqeltrrd.mm"
include "smfpimioompt.mm"
include "eqeltrd.mm"

theorem smfpimioo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume smfpimioo.s: |- ( ph -> S e. SAlg )
  assume smfpimioo.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfpimioo.d: |- D = dom F
  assume smfpimioo.a: |- ( ph -> A e. RR* )
  assume smfpimioo.b: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( `' F " ( A (,) B ) ) e. ( S |`t D ) )

  proof
    wph
    cF
    ccnv
    #
    cA
    cB
    cioo
    co
    #
    cima
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    vx
    cD
    crab
    #
    cS
    cD
    crest
    co
    wph
    @2
    vx
    cD
    @4
    cmpt
    #
    ccnv
    #
    @1
    cima
    #
    @5
    wph
    @0
    @7
    @1
    wph
    cF
    @6
    wph
    vx
    cD
    cr
    cF
    wph
    cD
    cS
    cF
    smfpimioo.s
    smfpimioo.f
    smfpimioo.d
    smff
    #
    feqmptd
    #
    cnveqd
    imaeq1d
    @8
    @5
    wceq
    wph
    vx
    cD
    @4
    @1
    @6
    @6
    eqid
    mptpreima
    a1i
    eqtrd
    wph
    vx
    cD
    @4
    cB
    cS
    cA
    cvv
    cr
    wph
    vx
    nfv
    smfpimioo.s
    wph
    cD
    cS
    cuni
    cvv
    wph
    cS
    csalg
    smfpimioo.s
    uniexd
    wph
    cD
    cS
    cF
    smfpimioo.s
    smfpimioo.f
    smfpimioo.d
    smfdmss
    ssexd
    wph
    cD
    cr
    @3
    cF
    @9
    ffvelrnda
    wph
    cF
    @6
    cS
    csmblfn
    cfv
    @10
    smfpimioo.f
    eqeltrrd
    smfpimioo.a
    smfpimioo.b
    smfpimioompt
    eqeltrd
end
