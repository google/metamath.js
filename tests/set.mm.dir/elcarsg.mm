include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "carsgval.mm"
include "eleq2d.mm"
include "ineq2.mm"
include "fveq2d.mm"
include "difeq2.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "simpr.mm"
include "adantr.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "ex.mm"
include "wb.mm"
include "elpwg.mm"
include "pm5.21ndd.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem elcarsg
  let wph: wff ph
  let cA: class A
  let ve: setvar e
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )

  disjoint M e
  disjoint O e
  disjoint e ph
  disjoint A e
  disjoint M a
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O m
  disjoint a ph
  disjoint m ph
  disjoint A a
  assert |- ( ph -> ( A e. ( toCaraSiga ` M ) <-> ( A C_ O /\ A. e e. ~P O ( ( M ` ( e i^i A ) ) +e ( M ` ( e \ A ) ) ) = ( M ` e ) ) ) )

  proof
    wph
    cA
    cM
    ccarsg
    cfv
    #
    wcel
    cA
    ve
    cv
    #
    va
    cv
    #
    cin
    #
    cM
    cfv
    #
    @1
    @2
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @1
    cM
    cfv
    #
    wceq
    #
    ve
    cO
    cpw
    #
    wral
    #
    va
    @10
    crab
    #
    wcel
    #
    cA
    cO
    wss
    #
    @1
    cA
    cin
    #
    cM
    cfv
    #
    @1
    cA
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @8
    wceq
    #
    ve
    @10
    wral
    #
    wa
    #
    wph
    @0
    @12
    cA
    wph
    ve
    cM
    cO
    cV
    va
    carsgval.1
    carsgval.2
    carsgval
    eleq2d
    @13
    cA
    @10
    wcel
    #
    @21
    wa
    wph
    @22
    @11
    @21
    va
    cA
    @10
    @2
    cA
    wceq
    #
    @9
    @20
    ve
    @10
    @24
    @7
    @19
    @8
    @24
    @4
    @16
    @6
    @18
    cxad
    @24
    @3
    @15
    cM
    @2
    cA
    @1
    ineq2
    fveq2d
    @24
    @5
    @17
    cM
    @2
    cA
    @1
    difeq2
    fveq2d
    oveq12d
    eqeq1d
    ralbidv
    elrab
    wph
    @23
    @14
    @21
    wph
    cA
    cvv
    wcel
    #
    @23
    @14
    @23
    @25
    wi
    wph
    cA
    @10
    elex
    a1i
    wph
    @14
    @25
    wph
    @14
    wa
    @14
    cO
    cV
    wcel
    #
    @25
    wph
    @14
    simpr
    wph
    @26
    @14
    carsgval.1
    adantr
    cA
    cO
    cV
    ssexg
    syl2anc
    ex
    @25
    @23
    @14
    wb
    wi
    wph
    cA
    cO
    cvv
    elpwg
    a1i
    pm5.21ndd
    anbi1d
    syl5bb
    bitrd
end
