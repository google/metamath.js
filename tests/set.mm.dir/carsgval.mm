include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "ccarsg.mm"
include "cmpt.mm"
include "df-carsg.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "dmeqd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "unipw.mm"
include "syl6eq.mm"
include "pweqd.mm"
include "wb.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "wcel.mm"
include "pwexg.mm"
include "fex.mm"
include "syl2anc.mm"
include "rabexg.mm"
include "3syl.mm"
include "fvmptd.mm"

theorem carsgval
  let wph: wff ph
  let ve: setvar e
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )

  disjoint M a
  disjoint M e
  disjoint a e
  disjoint O a
  disjoint O e
  disjoint a ph
  disjoint e ph
  disjoint M m
  disjoint a m
  disjoint e m
  disjoint O m
  disjoint m ph
  assert |- ( ph -> ( toCaraSiga ` M ) = { a e. ~P O | A. e e. ~P O ( ( M ` ( e i^i a ) ) +e ( M ` ( e \ a ) ) ) = ( M ` e ) } )

  proof
    wph
    vm
    cM
    ve
    cv
    #
    va
    cv
    #
    cin
    #
    vm
    cv
    #
    cfv
    #
    @0
    @1
    cdif
    #
    @3
    cfv
    #
    cxad
    co
    #
    @0
    @3
    cfv
    #
    wceq
    #
    ve
    @3
    cdm
    #
    cuni
    #
    cpw
    #
    wral
    #
    va
    @12
    crab
    #
    @2
    cM
    cfv
    #
    @5
    cM
    cfv
    #
    cxad
    co
    #
    @0
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
    @20
    crab
    #
    cvv
    ccarsg
    cvv
    ccarsg
    vm
    cvv
    @14
    cmpt
    wceq
    wph
    ve
    vm
    va
    df-carsg
    a1i
    wph
    @3
    cM
    wceq
    #
    wa
    #
    @13
    @21
    va
    @12
    @20
    @24
    @11
    cO
    @24
    @11
    @20
    cuni
    cO
    @24
    @10
    @20
    @24
    @10
    cM
    cdm
    #
    @20
    @24
    @3
    cM
    wph
    @23
    simpr
    dmeqd
    wph
    @25
    @20
    wceq
    #
    @23
    wph
    @20
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    #
    @26
    carsgval.2
    @20
    @27
    cM
    fdm
    syl
    adantr
    eqtrd
    unieqd
    cO
    unipw
    syl6eq
    pweqd
    #
    @24
    @9
    @19
    ve
    @12
    @20
    @29
    @23
    @9
    @19
    wb
    wph
    @23
    @7
    @17
    @8
    @18
    @23
    @4
    @15
    @6
    @16
    cxad
    @2
    @3
    cM
    fveq1
    @5
    @3
    cM
    fveq1
    oveq12d
    @0
    @3
    cM
    fveq1
    eqeq12d
    adantl
    raleqbidv
    rabeqbidv
    wph
    @28
    @20
    cvv
    wcel
    #
    cM
    cvv
    wcel
    carsgval.2
    wph
    cO
    cV
    wcel
    #
    @30
    carsgval.1
    cO
    cV
    pwexg
    #
    syl
    @20
    @27
    cvv
    cM
    fex
    syl2anc
    wph
    @31
    @30
    @22
    cvv
    wcel
    carsgval.1
    @32
    @21
    va
    @20
    cvv
    rabexg
    3syl
    fvmptd
end
