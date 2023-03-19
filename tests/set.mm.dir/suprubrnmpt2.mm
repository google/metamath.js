include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "elrnmpt1s.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "syl.mm"
include "rnmptbdd.mm"
include "suprubd.mm"

theorem suprubrnmpt2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  assume suprubrnmpt2.x: |- F/ x ph
  assume suprubrnmpt2.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume suprubrnmpt2.l: |- ( ph -> E. y e. RR A. x e. A B <_ y )
  assume suprubrnmpt2.c: |- ( ph -> C e. A )
  assume suprubrnmpt2.d: |- ( ph -> D e. RR )
  assume suprubrnmpt2.i: |- ( x = C -> B = D )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint B w
  assert |- ( ph -> D <_ sup ( ran ( x e. A |-> B ) , RR , < ) )

  proof
    wph
    vy
    vw
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cD
    wph
    vx
    cA
    cB
    cr
    @0
    suprubrnmpt2.x
    @0
    eqid
    #
    suprubrnmpt2.b
    rnmptssd
    wph
    cD
    @1
    wcel
    #
    @1
    c0
    wne
    wph
    cC
    cA
    wcel
    cD
    cr
    wcel
    @3
    suprubrnmpt2.c
    suprubrnmpt2.d
    vx
    cA
    cB
    cD
    cC
    @0
    cr
    @2
    suprubrnmpt2.i
    elrnmpt1s
    syl2anc
    #
    @1
    cD
    ne0i
    syl
    wph
    vx
    vy
    vw
    cA
    cB
    suprubrnmpt2.x
    suprubrnmpt2.l
    rnmptbdd
    @4
    suprubd
end
