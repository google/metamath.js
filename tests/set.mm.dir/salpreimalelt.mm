include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "csalg.mm"
include "adantr.mm"
include "cxr.mm"
include "adantlr.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cle.mm"
include "simpr.mm"
include "salpreimalegt.mm"
include "salpreimagtge.mm"
include "salpreimagelt.mm"

theorem salpreimalelt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume salpreimalelt.x: |- F/ x ph
  assume salpreimalelt.a: |- F/ a ph
  assume salpreimalelt.s: |- ( ph -> S e. SAlg )
  assume salpreimalelt.u: |- A = U. S
  assume salpreimalelt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimalelt.p: |- ( ( ph /\ a e. RR ) -> { x e. A | B <_ a } e. S )
  assume salpreimalelt.c: |- ( ph -> C e. RR )

  disjoint A a
  disjoint A x
  disjoint a x
  disjoint B a
  disjoint C a
  disjoint C x
  disjoint S a
  disjoint A b
  disjoint a b
  disjoint b x
  disjoint B b
  disjoint S b
  disjoint b ph
  disjoint k x
  assert |- ( ph -> { x e. A | B < C } e. S )

  proof
    wph
    vx
    cA
    cB
    cC
    cS
    va
    salpreimalelt.x
    salpreimalelt.a
    salpreimalelt.s
    salpreimalelt.u
    salpreimalelt.b
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    vx
    cA
    cB
    @0
    cS
    vb
    wph
    @1
    vx
    salpreimalelt.x
    @1
    vx
    nfv
    nfan
    @2
    vb
    nfv
    wph
    cS
    csalg
    wcel
    #
    @1
    salpreimalelt.s
    adantr
    wph
    vx
    cv
    cA
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    salpreimalelt.b
    adantlr
    wph
    vb
    cv
    #
    cr
    wcel
    #
    @6
    cB
    clt
    wbr
    vx
    cA
    crab
    cS
    wcel
    @1
    wph
    @7
    wa
    vx
    cA
    cB
    @6
    cS
    va
    wph
    @7
    vx
    salpreimalelt.x
    @7
    vx
    nfv
    nfan
    wph
    @7
    va
    salpreimalelt.a
    @7
    va
    nfv
    nfan
    wph
    @3
    @7
    salpreimalelt.s
    adantr
    salpreimalelt.u
    wph
    @4
    @5
    @7
    salpreimalelt.b
    adantlr
    wph
    @1
    cB
    @0
    cle
    wbr
    vx
    cA
    crab
    cS
    wcel
    @7
    salpreimalelt.p
    adantlr
    wph
    @7
    simpr
    salpreimalegt
    adantlr
    wph
    @1
    simpr
    salpreimagtge
    salpreimalelt.c
    salpreimagelt
end
