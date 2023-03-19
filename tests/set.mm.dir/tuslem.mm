include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "cunif.mm"
include "cutop.mm"
include "ctopn.mm"
include "cnx.mm"
include "cuni.mm"
include "cdm.mm"
include "cop.mm"
include "cpr.mm"
include "cts.mm"
include "csts.mm"
include "co.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "c9.mm"
include "1re.mm"
include "1lt9.mm"
include "ltneii.mm"
include "basendx.mm"
include "tsetndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "ustbas2.mm"
include "cvv.mm"
include "uniexg.mm"
include "dmexg.mm"
include "c3.mm"
include "cdc.mm"
include "eqid.mm"
include "df-unif.mm"
include "1nn.mm"
include "3nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "3nn.mm"
include "decnncl.mm"
include "2strbas.mm"
include "3syl.mm"
include "eqtrd.mm"
include "ctus.mm"
include "tusval.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "unifid.mm"
include "9re.mm"
include "9nn0.mm"
include "9lt10.mm"
include "gtneii.mm"
include "unifndx.mm"
include "2strop.mm"
include "prex.mm"
include "fvex.mm"
include "tsetid.mm"
include "setsid.mm"
include "mp2an.mm"
include "syl6reqr.mm"
include "crest.mm"
include "utopbas.mm"
include "unieqd.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "restid.mm"
include "ax-mp.mm"
include "topnval.mm"
include "3eqtr3g.mm"
include "3jca.mm"

theorem tuslem
  let cU: class U
  let cK: class K
  let cX: class X
  let vu: setvar u
  assume tuslem.k: |- K = ( toUnifSp ` U )


  assert |- ( U e. ( UnifOn ` X ) -> ( X = ( Base ` K ) /\ U = ( UnifSet ` K ) /\ ( unifTop ` U ) = ( TopOpen ` K ) ) )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    cX
    cK
    cbs
    cfv
    #
    wceq
    cU
    cK
    cunif
    cfv
    #
    wceq
    cU
    cutop
    cfv
    #
    cK
    ctopn
    cfv
    #
    wceq
    @1
    cnx
    cbs
    cfv
    #
    cU
    cuni
    #
    cdm
    #
    cop
    #
    cnx
    cunif
    cfv
    #
    cU
    cop
    #
    cpr
    #
    cbs
    cfv
    #
    @12
    cnx
    cts
    cfv
    #
    @4
    cop
    csts
    co
    #
    cbs
    cfv
    cX
    @2
    @4
    @14
    cbs
    @12
    baseid
    @6
    @14
    wne
    c1
    c9
    wne
    c1
    c9
    1re
    1lt9
    ltneii
    @6
    c1
    @14
    c9
    basendx
    tsetndx
    neeq12i
    mpbir
    setsnid
    @1
    cX
    @8
    @13
    cU
    cX
    ustbas2
    @1
    @7
    cvv
    wcel
    @8
    cvv
    wcel
    @8
    @13
    wceq
    cU
    @0
    uniexg
    @7
    cvv
    dmexg
    @8
    cU
    cunif
    @12
    c1
    c3
    cdc
    #
    cvv
    @12
    eqid
    #
    df-unif
    c1
    c3
    c1
    1nn
    3nn0
    1nn0
    1lt10
    declti
    #
    c1
    c3
    1nn0
    3nn
    decnncl
    #
    2strbas
    3syl
    eqtrd
    @1
    cK
    @15
    cbs
    @1
    cK
    cU
    ctus
    cfv
    @15
    tuslem.k
    cU
    cX
    tusval
    syl5eq
    #
    fveq2d
    3eqtr4a
    #
    @1
    @12
    cunif
    cfv
    @15
    cunif
    cfv
    cU
    @3
    @4
    @14
    cunif
    @12
    unifid
    @10
    @14
    wne
    @16
    c9
    wne
    c9
    @16
    9re
    c1
    c3
    c9
    1nn
    3nn0
    9nn0
    9lt10
    declti
    gtneii
    @10
    @16
    @14
    c9
    unifndx
    tsetndx
    neeq12i
    mpbir
    setsnid
    @8
    cU
    cunif
    @12
    @16
    @0
    @17
    df-unif
    @18
    @19
    2strop
    @1
    cK
    @15
    cunif
    @20
    fveq2d
    3eqtr4a
    @1
    @4
    cK
    cts
    cfv
    #
    @5
    @1
    @22
    @15
    cts
    cfv
    #
    @4
    @1
    cK
    @15
    cts
    @20
    fveq2d
    @12
    cvv
    wcel
    @4
    cvv
    wcel
    @4
    @23
    wceq
    @9
    @11
    prex
    cU
    cutop
    fvex
    cvv
    @4
    cts
    cvv
    @12
    tsetid
    setsid
    mp2an
    syl6reqr
    #
    @1
    @22
    @22
    cuni
    #
    crest
    co
    #
    @22
    @2
    crest
    co
    @22
    @5
    @1
    @25
    @2
    @22
    crest
    @1
    cX
    @4
    cuni
    @2
    @25
    cU
    cX
    utopbas
    @21
    @1
    @4
    @22
    @24
    unieqd
    3eqtr3rd
    oveq2d
    @22
    cvv
    wcel
    @26
    @22
    wceq
    cK
    cts
    fvex
    @22
    cvv
    @25
    @25
    eqid
    restid
    ax-mp
    @2
    @22
    cK
    @2
    eqid
    @22
    eqid
    topnval
    3eqtr3g
    eqtrd
    3jca
end
