include "wfn.mm"
include "wss.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "fvelimab.mm"
include "syl2anc.mm"

theorem fvelimabd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fvelimabd.1: |- ( ph -> F Fn A )
  assume fvelimabd.2: |- ( ph -> B C_ A )

  disjoint B x
  disjoint C x
  disjoint F x
  assert |- ( ph -> ( C e. ( F " B ) <-> E. x e. B ( F ` x ) = C ) )

  proof
    wph
    cF
    cA
    wfn
    cB
    cA
    wss
    cC
    cF
    cB
    cima
    wcel
    vx
    cv
    cF
    cfv
    cC
    wceq
    vx
    cB
    wrex
    wb
    fvelimabd.1
    fvelimabd.2
    vx
    cA
    cB
    cC
    cF
    fvelimab
    syl2anc
end
