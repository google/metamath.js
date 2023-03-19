include "wcel.mm"
include "csb.mm"
include "csbnestg.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "syl.mm"
include "csbeq1d.mm"
include "eqtrd.mm"

theorem csbco3g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let wph: wff ph
  assume sbcco3g.1: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ph x
  assert |- ( A e. V -> [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ D )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vy
    cB
    cD
    csb
    csb
    vy
    vx
    cA
    cB
    csb
    #
    cD
    csb
    vy
    cC
    cD
    csb
    vx
    vy
    cA
    cB
    cD
    cV
    csbnestg
    @0
    vy
    @1
    cC
    cD
    @0
    cA
    cvv
    wcel
    #
    @1
    cC
    wceq
    cA
    cV
    elex
    vx
    cA
    cB
    cC
    cvv
    @2
    vx
    cC
    nfcvd
    sbcco3g.1
    csbiegf
    syl
    csbeq1d
    eqtrd
end
