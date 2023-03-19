include "wss.mm"
include "wrex.mm"
include "ciin.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "iinss.mm"
include "syl.mm"

theorem iinssd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  assume iinssd.1: |- ( ph -> X e. A )
  assume iinssd.2: |- ( x = X -> B = D )
  assume iinssd.3: |- ( ph -> D C_ C )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint X x
  assert |- ( ph -> |^|_ x e. A B C_ C )

  proof
    wph
    cB
    cC
    wss
    #
    vx
    cA
    wrex
    #
    vx
    cA
    cB
    ciin
    cC
    wss
    wph
    cX
    cA
    wcel
    cD
    cC
    wss
    #
    @1
    iinssd.1
    iinssd.3
    @0
    @2
    vx
    cX
    cA
    vx
    cv
    cX
    wceq
    cB
    cD
    cC
    iinssd.2
    sseq1d
    rspcev
    syl2anc
    vx
    cA
    cB
    cC
    iinss
    syl
end
