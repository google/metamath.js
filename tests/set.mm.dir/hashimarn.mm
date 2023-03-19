include "cdm.mm"
include "crn.mm"
include "wf1.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "wceq.mm"
include "cres.mm"
include "wss.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "adantl.mm"
include "ssdmres.mm"
include "sylib.mm"
include "fveq2d.mm"
include "wfn.mm"
include "wfun.mm"
include "f1fun.mm"
include "funres.mm"
include "funfn.mm"
include "ad2antrr.mm"
include "hashfn.mm"
include "cvv.mm"
include "ovex.mm"
include "fex.mm"
include "sylancl.mm"
include "rnexg.mm"
include "simpll.mm"
include "f1ssres.mm"
include "syl2anc.mm"
include "hashf1rn.mm"
include "syl2an2.mm"
include "eqtr3d.mm"
include "df-ima.mm"
include "fveq2i.mm"
include "syl6reqr.mm"
include "mpan.mm"
include "3eqtr4d.mm"
include "ex.mm"

theorem hashimarn
  let cE: class E
  let cF: class F
  let cV: class V


  assert |- ( ( E : dom E -1-1-> ran E /\ E e. V ) -> ( F : ( 0 ..^ ( # ` F ) ) -1-1-> dom E -> ( # ` ( E " ran F ) ) = ( # ` F ) ) )

  proof
    cE
    cdm
    #
    cE
    crn
    #
    cE
    wf1
    #
    cE
    cV
    wcel
    #
    wa
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @0
    cF
    wf1
    #
    cE
    cF
    crn
    #
    cima
    #
    chash
    cfv
    #
    @5
    wceq
    @4
    @7
    wa
    #
    cE
    @8
    cres
    #
    cdm
    #
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    @10
    @5
    @11
    @13
    @8
    chash
    @11
    @8
    @0
    wss
    #
    @13
    @8
    wceq
    @7
    @16
    @4
    @7
    @6
    @0
    cF
    wf
    #
    @16
    @6
    @0
    cF
    f1f
    #
    @6
    @0
    cF
    frn
    syl
    adantl
    #
    @8
    cE
    ssdmres
    sylib
    fveq2d
    @11
    @14
    @12
    crn
    #
    chash
    cfv
    #
    @10
    @11
    @12
    chash
    cfv
    #
    @14
    @21
    @11
    @12
    @13
    wfn
    #
    @22
    @14
    wceq
    @2
    @23
    @3
    @7
    @2
    cE
    wfun
    #
    @23
    @0
    @1
    cE
    f1fun
    @24
    @12
    wfun
    @23
    @8
    cE
    funres
    @12
    funfn
    sylib
    syl
    ad2antrr
    @13
    @12
    hashfn
    syl
    @7
    @8
    cvv
    wcel
    #
    @4
    @8
    @1
    @12
    wf1
    #
    @22
    @21
    wceq
    @7
    cF
    cvv
    wcel
    #
    @25
    @7
    @17
    @6
    cvv
    wcel
    #
    @27
    @18
    cc0
    @5
    cfzo
    ovex
    #
    @6
    @0
    cvv
    cF
    fex
    sylancl
    cF
    cvv
    rnexg
    syl
    @11
    @2
    @16
    @26
    @2
    @3
    @7
    simpll
    @19
    @0
    @1
    @8
    cE
    f1ssres
    syl2anc
    @8
    @1
    @12
    cvv
    hashf1rn
    syl2an2
    eqtr3d
    @9
    @20
    chash
    cE
    @8
    df-ima
    fveq2i
    syl6reqr
    @7
    @5
    @15
    wceq
    #
    @4
    @28
    @7
    @30
    @29
    @6
    @0
    cF
    cvv
    hashf1rn
    mpan
    adantl
    3eqtr4d
    ex
end
