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
include "preimalegt.mm"
include "eqtr2d.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ancli.mm"
include "cv.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "sylc.mm"
include "saldifcld.mm"
include "eqeltrd.mm"

theorem salpreimalegt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let va: setvar a
  let vk: setvar k
  assume salpreimalegt.x: |- F/ x ph
  assume salpreimalegt.a: |- F/ a ph
  assume salpreimalegt.s: |- ( ph -> S e. SAlg )
  assume salpreimalegt.u: |- A = U. S
  assume salpreimalegt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume salpreimalegt.p: |- ( ( ph /\ a e. RR ) -> { x e. A | B <_ a } e. S )
  assume salpreimalegt.c: |- ( ph -> C e. RR )

  disjoint A a
  disjoint A x
  disjoint a x
  disjoint B a
  disjoint C a
  disjoint C x
  disjoint S a
  disjoint k x
  assert |- ( ph -> { x e. A | C < B } e. S )

  proof
    wph
    cC
    cB
    clt
    wbr
    vx
    cA
    crab
    #
    cS
    cuni
    #
    cB
    cC
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
    salpreimalegt.u
    eqcomi
    a1i
    difeq1d
    wph
    vx
    cA
    cB
    cC
    salpreimalegt.x
    salpreimalegt.b
    wph
    cC
    salpreimalegt.c
    rexrd
    preimalegt
    eqtr2d
    wph
    cS
    @3
    salpreimalegt.s
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
    salpreimalegt.c
    wph
    @5
    salpreimalegt.c
    ancli
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cB
    @8
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
    @6
    @7
    va
    wph
    @5
    va
    salpreimalegt.a
    @5
    va
    nfv
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
    @14
    @9
    @5
    wph
    @8
    cC
    cr
    eleq1
    anbi2d
    @14
    @12
    @3
    cS
    @14
    @11
    @2
    vx
    cA
    @8
    cC
    cB
    cle
    breq2
    rabbidv
    eleq1d
    imbi12d
    salpreimalegt.p
    vtoclgf
    sylc
    saldifcld
    eqeltrd
end
