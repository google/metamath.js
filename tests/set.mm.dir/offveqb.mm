include "cof.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wral.mm"
include "wfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "inidm.mm"
include "offval.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "fvexd.mm"
include "ralrimivw.mm"
include "mpteqb.mm"
include "syl.mm"
include "bitrd.mm"

theorem offveqb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  assume offveq.1: |- ( ph -> A e. V )
  assume offveq.2: |- ( ph -> F Fn A )
  assume offveq.3: |- ( ph -> G Fn A )
  assume offveq.4: |- ( ph -> H Fn A )
  assume offveq.5: |- ( ( ph /\ x e. A ) -> ( F ` x ) = B )
  assume offveq.6: |- ( ( ph /\ x e. A ) -> ( G ` x ) = C )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint ph x
  disjoint R x
  assert |- ( ph -> ( H = ( F oF R G ) <-> A. x e. A ( H ` x ) = ( B R C ) ) )

  proof
    wph
    cH
    cF
    cG
    cR
    cof
    co
    #
    wceq
    vx
    cA
    vx
    cv
    #
    cH
    cfv
    #
    cmpt
    #
    vx
    cA
    cB
    cC
    cR
    co
    #
    cmpt
    #
    wceq
    #
    @2
    @4
    wceq
    vx
    cA
    wral
    #
    wph
    cH
    @3
    @0
    @5
    wph
    cH
    cA
    wfn
    cH
    @3
    wceq
    offveq.4
    vx
    cA
    cH
    dffn5
    sylib
    wph
    vx
    cA
    cA
    cB
    cC
    cR
    cA
    cF
    cG
    cV
    cV
    offveq.2
    offveq.3
    offveq.1
    offveq.1
    cA
    inidm
    offveq.5
    offveq.6
    offval
    eqeq12d
    wph
    @2
    cvv
    wcel
    #
    vx
    cA
    wral
    @6
    @7
    wb
    wph
    @8
    vx
    cA
    wph
    @1
    cH
    fvexd
    ralrimivw
    vx
    cA
    @2
    @4
    cvv
    mpteqb
    syl
    bitrd
end
