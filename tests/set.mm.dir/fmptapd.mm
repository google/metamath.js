include "cmpt.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "fmptsnd.mm"
include "uneq2d.mm"
include "wceq.mm"
include "mptun.mm"
include "a1i.mm"
include "mpteq1d.mm"
include "3eqtr2d.mm"

theorem fmptapd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume fmptapd.0a: |- ( ph -> A e. _V )
  assume fmptapd.0b: |- ( ph -> B e. _V )
  assume fmptapd.1: |- ( ph -> ( R u. { A } ) = S )
  assume fmptapd.2: |- ( ( ph /\ x = A ) -> C = B )

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint S x
  disjoint ph x
  assert |- ( ph -> ( ( x e. R |-> C ) u. { <. A , B >. } ) = ( x e. S |-> C ) )

  proof
    wph
    vx
    cR
    cC
    cmpt
    #
    cA
    cB
    cop
    csn
    #
    cun
    @0
    vx
    cA
    csn
    #
    cC
    cmpt
    #
    cun
    #
    vx
    cR
    @2
    cun
    #
    cC
    cmpt
    #
    vx
    cS
    cC
    cmpt
    wph
    @1
    @3
    @0
    wph
    vx
    cA
    cC
    cB
    cvv
    cvv
    fmptapd.2
    fmptapd.0a
    fmptapd.0b
    fmptsnd
    uneq2d
    @6
    @4
    wceq
    wph
    vx
    cR
    @2
    cC
    mptun
    a1i
    wph
    vx
    @5
    cS
    cC
    fmptapd.1
    mpteq1d
    3eqtr2d
end
