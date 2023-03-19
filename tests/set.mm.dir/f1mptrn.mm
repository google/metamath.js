include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wreu.mm"
include "wa.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "ralrimiva.mm"
include "jca.mm"
include "wf1o.mm"
include "eqid.mm"
include "f1ompt.mm"
include "wfn.mm"
include "crn.mm"
include "dff1o2.mm"
include "simp2bi.mm"
include "sylbir.mm"
include "syl.mm"

theorem f1mptrn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume f1mptrn.1: |- ( ( ph /\ x e. A ) -> B e. C )
  assume f1mptrn.2: |- ( ( ph /\ y e. C ) -> E! x e. A y = B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> Fun `' ( x e. A |-> B ) )

  proof
    wph
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cv
    cB
    wceq
    vx
    cA
    wreu
    #
    vy
    cC
    wral
    #
    wa
    #
    vx
    cA
    cB
    cmpt
    #
    ccnv
    wfun
    #
    wph
    @1
    @3
    wph
    @0
    vx
    cA
    f1mptrn.1
    ralrimiva
    wph
    @2
    vy
    cC
    f1mptrn.2
    ralrimiva
    jca
    @4
    cA
    cC
    @5
    wf1o
    #
    @6
    vx
    vy
    cA
    cC
    cB
    @5
    @5
    eqid
    f1ompt
    @7
    @5
    cA
    wfn
    @6
    @5
    crn
    cC
    wceq
    cA
    cC
    @5
    dff1o2
    simp2bi
    sylbir
    syl
end
