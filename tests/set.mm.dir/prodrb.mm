include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wb.mm"
include "prodrblem2.mm"
include "wa.mm"
include "bicomd.mm"
include "cz.mm"
include "wo.mm"
include "uztric.mm"
include "syl2anc.mm"
include "mpjaodan.mm"

theorem prodrb
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
  assert |- ( ph -> ( seq M ( x. , F ) ~~> C <-> seq N ( x. , F ) ~~> C ) )

  proof
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    cmul
    cF
    cM
    cseq
    cC
    cli
    wbr
    #
    cmul
    cF
    cN
    cseq
    cC
    cli
    wbr
    #
    wb
    cM
    cN
    cuz
    cfv
    wcel
    #
    wph
    cA
    cB
    cC
    vk
    cF
    cM
    cN
    prodmo.1
    prodmo.2
    prodrb.4
    prodrb.5
    prodrb.6
    prodrb.7
    prodrblem2
    wph
    @3
    wa
    @2
    @1
    wph
    cA
    cB
    cC
    vk
    cF
    cN
    cM
    prodmo.1
    prodmo.2
    prodrb.5
    prodrb.4
    prodrb.7
    prodrb.6
    prodrblem2
    bicomd
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    @0
    @3
    wo
    prodrb.4
    prodrb.5
    cM
    cN
    uztric
    syl2anc
    mpjaodan
end
