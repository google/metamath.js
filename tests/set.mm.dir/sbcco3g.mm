include "wcel.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcnestg.mm"
include "cvv.mm"
include "wceq.mm"
include "wb.mm"
include "elex.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "dfsbcq.mm"
include "3syl.mm"
include "bitrd.mm"

theorem sbcco3g
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cD: class D
  assume sbcco3g.1: |- ( x = A -> B = C )

  disjoint A x
  disjoint ph x
  disjoint C x
  disjoint D x
  assert |- ( A e. V -> ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) )

  proof
    cA
    cV
    wcel
    #
    wph
    vy
    cB
    wsbc
    vx
    cA
    wsbc
    wph
    vy
    vx
    cA
    cB
    csb
    #
    wsbc
    #
    wph
    vy
    cC
    wsbc
    #
    wph
    vx
    vy
    cA
    cB
    cV
    sbcnestg
    @0
    cA
    cvv
    wcel
    #
    @1
    cC
    wceq
    @2
    @3
    wb
    cA
    cV
    elex
    vx
    cA
    cB
    cC
    cvv
    @4
    vx
    cC
    nfcvd
    sbcco3g.1
    csbiegf
    wph
    vy
    @1
    cC
    dfsbcq
    3syl
    bitrd
end
