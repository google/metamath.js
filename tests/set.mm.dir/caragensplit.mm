include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "pweqi.mm"
include "syl6eleq.mm"
include "wa.mm"
include "caragenel.mm"
include "mpbid.mm"
include "simprd.mm"
include "ineq1.mm"
include "fveq2d.mm"
include "difeq1.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcva.mm"

theorem caragensplit
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cO: class O
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragensplit.o: |- ( ph -> O e. OutMeas )
  assume caragensplit.s: |- S = ( CaraGen ` O )
  assume caragensplit.x: |- X = U. dom O
  assume caragensplit.e: |- ( ph -> E e. S )
  assume caragensplit.a: |- ( ph -> A C_ X )


  assert |- ( ph -> ( ( O ` ( A i^i E ) ) +e ( O ` ( A \ E ) ) ) = ( O ` A ) )

  proof
    wph
    cA
    cO
    cdm
    cuni
    #
    cpw
    #
    wcel
    va
    cv
    #
    cE
    cin
    #
    cO
    cfv
    #
    @2
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @2
    cO
    cfv
    #
    wceq
    #
    va
    @1
    wral
    #
    cA
    cE
    cin
    #
    cO
    cfv
    #
    cA
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    cA
    cO
    cfv
    #
    wceq
    #
    wph
    cA
    cX
    cpw
    #
    @1
    wph
    cA
    @18
    wcel
    #
    cA
    cX
    wss
    #
    caragensplit.a
    wph
    cA
    cvv
    wcel
    #
    @19
    @20
    wb
    wph
    @20
    cX
    cvv
    wcel
    @21
    caragensplit.a
    wph
    cO
    come
    cX
    caragensplit.o
    caragensplit.x
    unidmex
    cA
    cX
    cvv
    ssexg
    syl2anc
    cA
    cX
    cvv
    elpwg
    syl
    mpbird
    cX
    @0
    caragensplit.x
    pweqi
    syl6eleq
    wph
    cE
    @1
    wcel
    #
    @10
    wph
    cE
    cS
    wcel
    @22
    @10
    wa
    caragensplit.e
    wph
    cS
    cE
    cO
    va
    caragensplit.o
    caragensplit.s
    caragenel
    mpbid
    simprd
    @9
    @17
    va
    cA
    @1
    @2
    cA
    wceq
    #
    @7
    @15
    @8
    @16
    @23
    @4
    @12
    @6
    @14
    cxad
    @23
    @3
    @11
    cO
    @2
    cA
    cE
    ineq1
    fveq2d
    @23
    @5
    @13
    cO
    @2
    cA
    cE
    difeq1
    fveq2d
    oveq12d
    @2
    cA
    cO
    fveq2
    eqeq12d
    rspcva
    syl2anc
end
