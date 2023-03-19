include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "wss.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "adantr.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "rnmptbdd.mm"
include "suprubd.mm"

theorem suprubrnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume suprubrnmpt.x: |- F/ x ph
  assume suprubrnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume suprubrnmpt.e: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint B w
  assert |- ( ( ph /\ x e. A ) -> B <_ sup ( ran ( x e. A |-> B ) , RR , < ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vy
    vw
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cB
    wph
    @3
    cr
    wss
    @0
    wph
    vx
    cA
    cB
    cr
    @2
    suprubrnmpt.x
    @2
    eqid
    #
    suprubrnmpt.b
    rnmptssd
    adantr
    @1
    cB
    @3
    wcel
    #
    @3
    c0
    wne
    @1
    @0
    cB
    cr
    wcel
    @5
    wph
    @0
    simpr
    suprubrnmpt.b
    vx
    cA
    cB
    @2
    cr
    @4
    elrnmpt1
    syl2anc
    #
    @3
    cB
    ne0i
    syl
    wph
    vw
    cv
    vy
    cv
    cle
    wbr
    vw
    @3
    wral
    vy
    cr
    wrex
    @0
    wph
    vx
    vy
    vw
    cA
    cB
    suprubrnmpt.x
    suprubrnmpt.e
    rnmptbdd
    adantr
    @6
    suprubd
end
