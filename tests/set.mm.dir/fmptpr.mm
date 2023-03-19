include "cop.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-pr.mm"
include "a1i.mm"
include "fmptsnd.mm"
include "uneq1d.mm"
include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "eqcomi.mm"
include "fmptapd.mm"
include "3eqtrd.mm"

theorem fmptpr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume fmptpr.1: |- ( ph -> A e. V )
  assume fmptpr.2: |- ( ph -> B e. W )
  assume fmptpr.3: |- ( ph -> C e. X )
  assume fmptpr.4: |- ( ph -> D e. Y )
  assume fmptpr.5: |- ( ( ph /\ x = A ) -> E = C )
  assume fmptpr.6: |- ( ( ph /\ x = B ) -> E = D )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( ph -> { <. A , C >. , <. B , D >. } = ( x e. { A , B } |-> E ) )

  proof
    wph
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    @0
    csn
    #
    @1
    csn
    #
    cun
    #
    vx
    cA
    csn
    #
    cE
    cmpt
    #
    @4
    cun
    vx
    cA
    cB
    cpr
    #
    cE
    cmpt
    @2
    @5
    wceq
    wph
    @0
    @1
    df-pr
    a1i
    wph
    @3
    @7
    @4
    wph
    vx
    cA
    cE
    cC
    cV
    cX
    fmptpr.5
    fmptpr.1
    fmptpr.3
    fmptsnd
    uneq1d
    wph
    vx
    cB
    cD
    cE
    @6
    @8
    wph
    cB
    cW
    wcel
    cB
    cvv
    wcel
    fmptpr.2
    cB
    cW
    elex
    syl
    wph
    cD
    cY
    wcel
    cD
    cvv
    wcel
    fmptpr.4
    cD
    cY
    elex
    syl
    @6
    cB
    csn
    cun
    #
    @8
    wceq
    wph
    @8
    @9
    cA
    cB
    df-pr
    eqcomi
    a1i
    fmptpr.6
    fmptapd
    3eqtrd
end
