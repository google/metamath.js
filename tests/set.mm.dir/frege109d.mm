include "cima.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "trclfvlb.mm"
include "imass1.mm"
include "3syl.mm"
include "coss1.mm"
include "trclfvcotrg.mm"
include "syl6ss.mm"
include "syl.mm"
include "unssd.mm"
include "ssun2.mm"
include "imaeq2d.mm"
include "imaundi.mm"
include "imaco.mm"
include "eqcomi.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "3sstr4d.mm"

theorem frege109d
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cU: class U
  assume frege109d.r: |- ( ph -> R e. _V )
  assume frege109d.a: |- ( ph -> A = ( U u. ( ( t+ ` R ) " U ) ) )


  assert |- ( ph -> ( R " A ) C_ A )

  proof
    wph
    cR
    cU
    cima
    #
    cR
    cR
    ctcl
    cfv
    #
    ccom
    #
    cU
    cima
    #
    cun
    #
    cU
    @1
    cU
    cima
    #
    cun
    #
    cR
    cA
    cima
    #
    cA
    wph
    @4
    @5
    @6
    wph
    @0
    @3
    @5
    wph
    cR
    cvv
    wcel
    #
    cR
    @1
    wss
    #
    @0
    @5
    wss
    frege109d.r
    cR
    cvv
    trclfvlb
    #
    cR
    @1
    cU
    imass1
    3syl
    wph
    @2
    @1
    wss
    @3
    @5
    wss
    wph
    @2
    @1
    @1
    ccom
    #
    @1
    wph
    @8
    @9
    @2
    @11
    wss
    frege109d.r
    @10
    cR
    @1
    @1
    coss1
    3syl
    cR
    trclfvcotrg
    syl6ss
    @2
    @1
    cU
    imass1
    syl
    unssd
    @5
    cU
    ssun2
    syl6ss
    wph
    @7
    cR
    @6
    cima
    #
    @4
    wph
    cA
    @6
    cR
    frege109d.a
    imaeq2d
    @12
    @0
    cR
    @5
    cima
    #
    cun
    @4
    cR
    cU
    @5
    imaundi
    @13
    @3
    @0
    @3
    @13
    cR
    @1
    cU
    imaco
    eqcomi
    uneq2i
    eqtri
    syl6eq
    frege109d.a
    3sstr4d
end
