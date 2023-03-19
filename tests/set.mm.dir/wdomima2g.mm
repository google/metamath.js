include "wfun.mm"
include "wcel.mm"
include "cima.mm"
include "w3a.mm"
include "cres.mm"
include "crn.mm"
include "cwdom.mm"
include "df-ima.mm"
include "cdm.mm"
include "wbr.mm"
include "cvv.mm"
include "wfo.mm"
include "wf.mm"
include "funres.mm"
include "funforn.mm"
include "sylib.mm"
include "3ad2ant1.mm"
include "fof.mm"
include "syl.mm"
include "wss.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "simp2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "simp3.mm"
include "syl5eqelr.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fowdom.mm"
include "syl2anc.mm"
include "cdom.mm"
include "ssdomg.mm"
include "mpi.mm"
include "domwdom.mm"
include "3ad2ant2.mm"
include "wdomtr.mm"
include "syl5eqbr.mm"

theorem wdomima2g
  let cA: class A
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( Fun F /\ A e. V /\ ( F " A ) e. W ) -> ( F " A ) ~<_* A )

  proof
    cF
    wfun
    #
    cA
    cV
    wcel
    #
    cF
    cA
    cima
    #
    cW
    wcel
    #
    w3a
    #
    @2
    cF
    cA
    cres
    #
    crn
    #
    cA
    cwdom
    cF
    cA
    df-ima
    #
    @4
    @6
    @5
    cdm
    #
    cwdom
    wbr
    #
    @8
    cA
    cwdom
    wbr
    #
    @6
    cA
    cwdom
    wbr
    @4
    @5
    cvv
    wcel
    #
    @8
    @6
    @5
    wfo
    #
    @9
    @4
    @8
    @6
    @5
    wf
    #
    @8
    cvv
    wcel
    #
    @6
    cW
    wcel
    @11
    @4
    @12
    @13
    @0
    @1
    @12
    @3
    @0
    @5
    wfun
    @12
    cA
    cF
    funres
    @5
    funforn
    sylib
    3ad2ant1
    #
    @8
    @6
    @5
    fof
    syl
    @4
    @8
    cA
    wss
    #
    @1
    @14
    @8
    cA
    cF
    cdm
    #
    cin
    cA
    cF
    cA
    dmres
    cA
    @17
    inss1
    eqsstri
    #
    @0
    @1
    @3
    simp2
    @8
    cA
    cV
    ssexg
    sylancr
    @4
    @6
    @2
    cW
    @7
    @0
    @1
    @3
    simp3
    syl5eqelr
    @8
    @6
    @5
    cvv
    cW
    fex2
    syl3anc
    @15
    @5
    cvv
    @6
    @8
    fowdom
    syl2anc
    @1
    @0
    @10
    @3
    @1
    @8
    cA
    cdom
    wbr
    #
    @10
    @1
    @16
    @19
    @18
    @8
    cA
    cV
    ssdomg
    mpi
    @8
    cA
    domwdom
    syl
    3ad2ant2
    @6
    @8
    cA
    wdomtr
    syl2anc
    syl5eqbr
end
