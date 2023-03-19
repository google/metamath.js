include "come.mm"
include "wcel.mm"
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
include "ccaragen.mm"
include "id.mm"
include "dmexg.mm"
include "uniexg.mm"
include "syl.mm"
include "pwexg.mm"
include "rabexg.mm"
include "dmeq.mm"
include "unieqd.mm"
include "pweqd.mm"
include "raleqdv.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "rabeqbidv.mm"
include "df-caragen.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem caragenval
  let ve: setvar e
  let cO: class O
  let va: setvar a
  let vo: setvar o
  let vk: setvar k
  let vx: setvar x

  disjoint O a
  disjoint O e
  disjoint a e
  disjoint O o
  disjoint a o
  disjoint e o
  disjoint k x
  assert |- ( O e. OutMeas -> ( CaraGen ` O ) = { e e. ~P U. dom O | A. a e. ~P U. dom O ( ( O ` ( a i^i e ) ) +e ( O ` ( a \ e ) ) ) = ( O ` a ) } )

  proof
    cO
    come
    wcel
    #
    @0
    va
    cv
    #
    ve
    cv
    #
    cin
    #
    cO
    cfv
    #
    @1
    @2
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @1
    cO
    cfv
    #
    wceq
    #
    va
    cO
    cdm
    #
    cuni
    #
    cpw
    #
    wral
    #
    ve
    @12
    crab
    #
    cvv
    wcel
    #
    cO
    ccaragen
    cfv
    @14
    wceq
    @0
    id
    @0
    @12
    cvv
    wcel
    #
    @15
    @0
    @11
    cvv
    wcel
    #
    @16
    @0
    @10
    cvv
    wcel
    @17
    cO
    come
    dmexg
    @10
    cvv
    uniexg
    syl
    @11
    cvv
    pwexg
    syl
    @13
    ve
    @12
    cvv
    rabexg
    syl
    vo
    cO
    @3
    vo
    cv
    #
    cfv
    #
    @5
    @18
    cfv
    #
    cxad
    co
    #
    @1
    @18
    cfv
    #
    wceq
    #
    va
    @18
    cdm
    #
    cuni
    #
    cpw
    #
    wral
    #
    ve
    @26
    crab
    @14
    come
    cvv
    ccaragen
    @18
    cO
    wceq
    #
    @27
    @13
    ve
    @26
    @12
    @28
    @25
    @11
    @28
    @24
    @10
    @18
    cO
    dmeq
    unieqd
    pweqd
    #
    @28
    @27
    @23
    va
    @12
    wral
    @13
    @28
    @23
    va
    @26
    @12
    @29
    raleqdv
    @28
    @23
    @9
    va
    @12
    @28
    @21
    @7
    @22
    @8
    @28
    @19
    @4
    @20
    @6
    cxad
    @3
    @18
    cO
    fveq1
    @5
    @18
    cO
    fveq1
    oveq12d
    @1
    @18
    cO
    fveq1
    eqeq12d
    ralbidv
    bitrd
    rabeqbidv
    ve
    vo
    va
    df-caragen
    fvmptg
    syl2anc
end
