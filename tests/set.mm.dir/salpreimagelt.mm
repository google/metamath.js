include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cuni.mm"
include "cle.mm"
include "cdif.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "difeq1d.mm"
include "rexrd.mm"
include "preimagelt.mm"
include "eqtr2d.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "id.mm"
include "jca.mm"
include "cv.mm"
include "wi.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfan.mm"
include "nfv.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq1.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "saldifcld.mm"
include "eqeltrd.mm"

theorem salpreimagelt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vk: setvar k
  assume salpreimagelt.x: |- F/ x ph
  assume salpreimagelt.a: |- F/ a ph
  assume salpreimagelt.s: |- ( ph -> S e. SAlg )
  assume salpreimagelt.u: |- A = U. S
  assume salpreimagelt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimagelt.p: |- ( ( ph /\ a e. RR ) -> { x e. A | a <_ B } e. S )
  assume salpreimagelt.c: |- ( ph -> C e. RR )

  disjoint A a
  disjoint A x
  disjoint a x
  disjoint B a
  disjoint C a
  disjoint C x
  disjoint S a
  disjoint k x
  assert |- ( ph -> { x e. A | B < C } e. S )

  proof
    wph
    cB
    cC
    clt
    wbr
    vx
    cA
    crab
    #
    cS
    cuni
    #
    cC
    cB
    cle
    wbr
    #
    vx
    cA
    crab
    #
    cdif
    #
    cS
    wph
    @4
    cA
    @3
    cdif
    @0
    wph
    @1
    cA
    @3
    @1
    cA
    wceq
    wph
    cA
    @1
    salpreimagelt.u
    eqcomi
    a1i
    difeq1d
    wph
    vx
    cA
    cB
    cC
    salpreimagelt.x
    salpreimagelt.b
    wph
    cC
    salpreimagelt.c
    rexrd
    preimagelt
    eqtr2d
    wph
    cS
    @3
    salpreimagelt.s
    wph
    cC
    cr
    wcel
    #
    wph
    @5
    wa
    #
    @3
    cS
    wcel
    #
    salpreimagelt.c
    wph
    wph
    @5
    wph
    id
    salpreimagelt.c
    jca
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    @8
    cB
    cle
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
    @6
    @7
    wi
    va
    cC
    cr
    va
    cC
    nfcv
    #
    @6
    @7
    va
    wph
    @5
    va
    salpreimagelt.a
    va
    cC
    cr
    @14
    nfel1
    nfan
    @7
    va
    nfv
    nfim
    @8
    cC
    wceq
    #
    @10
    @6
    @13
    @7
    @15
    @9
    @5
    wph
    @8
    cC
    cr
    eleq1
    anbi2d
    @15
    @12
    @3
    cS
    @15
    @11
    @2
    vx
    cA
    @8
    cC
    cB
    cle
    breq1
    rabbidv
    eleq1d
    imbi12d
    salpreimagelt.p
    vtoclgf
    sylc
    saldifcld
    eqeltrd
end
