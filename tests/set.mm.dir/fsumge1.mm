include "csn.mm"
include "csu.mm"
include "cle.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "recnd.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "snssd.mm"
include "fsumless.mm"
include "eqbrtrrd.mm"

theorem fsumge1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cM: class M
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume fsumge0.1: |- ( ph -> A e. Fin )
  assume fsumge0.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumge0.3: |- ( ( ph /\ k e. A ) -> 0 <_ B )
  assume fsumge1.4: |- ( k = M -> B = C )
  assume fsumge1.5: |- ( ph -> M e. A )

  disjoint A k
  disjoint C k
  disjoint M k
  disjoint k ph
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B x
  disjoint B y
  disjoint m ph
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> C <_ sum_ k e. A B )

  proof
    wph
    cM
    csn
    #
    cB
    vk
    csu
    #
    cC
    cA
    cB
    vk
    csu
    cle
    wph
    cM
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    @1
    cC
    wceq
    fsumge1.5
    wph
    @2
    cB
    cc
    wcel
    #
    vk
    cA
    wral
    @3
    fsumge1.5
    wph
    @4
    vk
    cA
    wph
    vk
    cv
    #
    cA
    wcel
    wa
    cB
    fsumge0.2
    recnd
    ralrimiva
    @4
    @3
    vk
    cM
    cA
    @5
    cM
    wceq
    cB
    cC
    cc
    fsumge1.4
    eleq1d
    rspcv
    sylc
    cB
    cC
    vk
    cM
    cA
    fsumge1.4
    sumsn
    syl2anc
    wph
    cA
    cB
    @0
    vk
    fsumge0.1
    fsumge0.2
    fsumge0.3
    wph
    cM
    cA
    fsumge1.5
    snssd
    fsumless
    eqbrtrrd
end
