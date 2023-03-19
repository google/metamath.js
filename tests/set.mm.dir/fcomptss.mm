include "wf.mm"
include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fssd.mm"
include "fcompt.mm"
include "syl2anc.mm"

theorem fcomptss
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume fcomptss.a: |- ( ph -> F : A --> B )
  assume fcomptss.b: |- ( ph -> B C_ C )
  assume fcomptss.g: |- ( ph -> G : C --> D )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint G x
  assert |- ( ph -> ( G o. F ) = ( x e. A |-> ( G ` ( F ` x ) ) ) )

  proof
    wph
    cC
    cD
    cG
    wf
    cA
    cC
    cF
    wf
    cG
    cF
    ccom
    vx
    cA
    vx
    cv
    cF
    cfv
    cG
    cfv
    cmpt
    wceq
    fcomptss.g
    wph
    cA
    cB
    cC
    cF
    fcomptss.a
    fcomptss.b
    fssd
    vx
    cG
    cF
    cA
    cC
    cD
    fcompt
    syl2anc
end
