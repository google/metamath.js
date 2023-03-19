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
include "wi.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq1.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "simpr.mm"
include "salpreimagtge.mm"
include "salpreimagelt.mm"

theorem salpreimagtlt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  assume salpreimagtlt.x: |- F/ x ph
  assume salpreimagtlt.a: |- F/ a ph
  assume salpreimagtlt.s: |- ( ph -> S e. SAlg )
  assume salpreimagtlt.u: |- A = U. S
  assume salpreimagtlt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimagtlt.p: |- ( ( ph /\ a e. RR ) -> { x e. A | a < B } e. S )
  assume salpreimagtlt.c: |- ( ph -> C e. RR )

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
    salpreimagtlt.x
    salpreimagtlt.a
    salpreimagtlt.s
    salpreimagtlt.u
    salpreimagtlt.b
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
    salpreimagtlt.x
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
    @1
    salpreimagtlt.s
    adantr
    wph
    vx
    cv
    cA
    wcel
    cB
    cxr
    wcel
    @1
    salpreimagtlt.b
    adantlr
    wph
    vb
    cv
    #
    cr
    wcel
    #
    @3
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cS
    wcel
    #
    @1
    @2
    @0
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cS
    wcel
    #
    wi
    wph
    @4
    wa
    #
    @7
    wi
    va
    vb
    @11
    @7
    va
    wph
    @4
    va
    salpreimagtlt.a
    @4
    va
    nfv
    nfan
    @7
    va
    nfv
    nfim
    @0
    @3
    wceq
    #
    @2
    @11
    @10
    @7
    @12
    @1
    @4
    wph
    @0
    @3
    cr
    eleq1
    anbi2d
    @12
    @9
    @6
    cS
    @12
    @8
    @5
    vx
    cA
    @0
    @3
    cB
    clt
    breq1
    rabbidv
    eleq1d
    imbi12d
    salpreimagtlt.p
    chvar
    adantlr
    wph
    @1
    simpr
    salpreimagtge
    salpreimagtlt.c
    salpreimagelt
end
