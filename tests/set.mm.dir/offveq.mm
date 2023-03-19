include "cof.mm"
include "co.mm"
include "inidm.mm"
include "offn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "ofval.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem offveq
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
  assume offveq.7: |- ( ( ph /\ x e. A ) -> ( B R C ) = ( H ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint ph x
  disjoint R x
  assert |- ( ph -> ( F oF R G ) = H )

  proof
    wph
    vx
    cA
    cF
    cG
    cR
    cof
    co
    #
    cH
    wph
    cA
    cA
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
    #
    offn
    offveq.4
    wph
    vx
    cv
    #
    cA
    wcel
    wa
    @2
    @0
    cfv
    cB
    cC
    cR
    co
    @2
    cH
    cfv
    wph
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
    @2
    offveq.2
    offveq.3
    offveq.1
    offveq.1
    @1
    offveq.5
    offveq.6
    ofval
    offveq.7
    eqtrd
    eqfnfvd
end
