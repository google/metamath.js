include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "cseq.mm"
include "cres.mm"
include "cli.mm"
include "wbr.mm"
include "cz.mm"
include "cvv.mm"
include "wb.mm"
include "adantr.mm"
include "seqex.mm"
include "climres.mm"
include "sylancl.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "cc.mm"
include "adantlr.mm"
include "simpr.mm"
include "prodrblem.mm"
include "mpidan.mm"
include "breq1d.mm"
include "bitr3d.mm"

theorem prodrblem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodrb.4: |- ( ph -> M e. ZZ )
  assume prodrb.5: |- ( ph -> N e. ZZ )
  assume prodrb.6: |- ( ph -> A C_ ( ZZ>= ` M ) )
  assume prodrb.7: |- ( ph -> A C_ ( ZZ>= ` N ) )

  disjoint N k
  disjoint M k
  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint A n
  disjoint k n
  disjoint F n
  disjoint n ph
  disjoint M n
  disjoint N n
  assert |- ( ( ph /\ N e. ( ZZ>= ` M ) ) -> ( seq M ( x. , F ) ~~> C <-> seq N ( x. , F ) ~~> C ) )

  proof
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    wa
    #
    cmul
    cF
    cM
    cseq
    #
    cN
    cuz
    cfv
    #
    cres
    #
    cC
    cli
    wbr
    #
    @2
    cC
    cli
    wbr
    #
    cmul
    cF
    cN
    cseq
    #
    cC
    cli
    wbr
    @1
    cN
    cz
    wcel
    #
    @2
    cvv
    wcel
    @5
    @6
    wb
    wph
    @8
    @0
    prodrb.5
    adantr
    cmul
    cF
    cM
    seqex
    cC
    @2
    cN
    cvv
    climres
    sylancl
    @1
    @4
    @7
    cC
    cli
    wph
    @0
    cA
    @3
    wss
    @4
    @7
    wceq
    prodrb.7
    @1
    cA
    cB
    vk
    cF
    cM
    cN
    prodmo.1
    wph
    vk
    cv
    cA
    wcel
    cB
    cc
    wcel
    @0
    prodmo.2
    adantlr
    wph
    @0
    simpr
    prodrblem
    mpidan
    breq1d
    bitr3d
end
