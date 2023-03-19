include "wcel.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "pweqi.mm"
include "syl6eleq.mm"
include "simpl.mm"
include "eleq2i.mm"
include "bicomi.mm"
include "biimpi.mm"
include "adantl.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "caragenel.mm"
include "mpbird.mm"

theorem carageneld
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cO: class O
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume carageneld.o: |- ( ph -> O e. OutMeas )
  assume carageneld.x: |- X = U. dom O
  assume carageneld.s: |- S = ( CaraGen ` O )
  assume carageneld.e: |- ( ph -> E e. ~P X )
  assume carageneld.a: |- ( ( ph /\ a e. ~P X ) -> ( ( O ` ( a i^i E ) ) +e ( O ` ( a \ E ) ) ) = ( O ` a ) )

  disjoint E a
  disjoint O a
  disjoint a ph
  disjoint k x
  assert |- ( ph -> E e. S )

  proof
    wph
    cE
    cS
    wcel
    cE
    cO
    cdm
    cuni
    #
    cpw
    #
    wcel
    #
    va
    cv
    #
    cE
    cin
    cO
    cfv
    @3
    cE
    cdif
    cO
    cfv
    cxad
    co
    @3
    cO
    cfv
    wceq
    #
    va
    @1
    wral
    #
    wa
    wph
    @2
    @5
    wph
    cE
    cX
    cpw
    #
    @1
    carageneld.e
    cX
    @0
    carageneld.x
    pweqi
    #
    syl6eleq
    wph
    @4
    va
    @1
    wph
    @3
    @1
    wcel
    #
    wa
    wph
    @3
    @6
    wcel
    #
    @4
    wph
    @8
    simpl
    @8
    @9
    wph
    @8
    @9
    @9
    @8
    @6
    @1
    @3
    @7
    eleq2i
    bicomi
    biimpi
    adantl
    carageneld.a
    syl2anc
    ralrimiva
    jca
    wph
    cS
    cE
    cO
    va
    carageneld.o
    carageneld.s
    caragenel
    mpbird
end
