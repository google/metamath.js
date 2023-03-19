include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c0p.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cle.mm"
include "cc0.mm"
include "cdgr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "dgr0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "nn0ge0.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "csn.mm"
include "cxp.mm"
include "ccoe.mm"
include "coe0.mm"
include "fveq1d.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqtrd.mm"
include "jca.mm"
include "cr.mm"
include "wi.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "nn0red.mm"
include "nn0re.mm"
include "ltle.mm"
include "syl2an.mm"
include "imp.mm"
include "wne.mm"
include "wn.mm"
include "dgrub.mm"
include "3expia.mm"
include "wb.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "sylibd.mm"
include "necon4ad.mm"
include "jaodan.mm"
include "leloe.mm"
include "biimpa.mm"
include "adantrr.mm"
include "fveq2.mm"
include "dgreq0.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "syl5ibr.mm"
include "orim2d.mm"
include "mpd.mm"
include "orcomd.mm"
include "impbida.mm"

theorem dgrlt
  let cA: class A
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vz: setvar z
  assume dgreq0.1: |- N = ( deg ` F )
  assume dgreq0.2: |- A = ( coeff ` F )


  assert |- ( ( F e. ( Poly ` S ) /\ M e. NN0 ) -> ( ( F = 0p \/ N < M ) <-> ( N <_ M /\ ( A ` M ) = 0 ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    cF
    c0p
    wceq
    #
    cN
    cM
    clt
    wbr
    #
    wo
    cN
    cM
    cle
    wbr
    #
    cM
    cA
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @2
    @3
    @8
    @4
    @2
    @3
    wa
    #
    @5
    @7
    @9
    cN
    cc0
    cM
    cle
    @9
    cF
    cdgr
    cfv
    #
    c0p
    cdgr
    cfv
    #
    cN
    cc0
    @9
    cF
    c0p
    cdgr
    @2
    @3
    simpr
    #
    fveq2d
    dgreq0.1
    @11
    cc0
    dgr0
    eqcomi
    3eqtr4g
    @1
    cc0
    cM
    cle
    wbr
    @0
    @3
    cM
    nn0ge0
    ad2antlr
    eqbrtrd
    @9
    @6
    cM
    cn0
    cc0
    csn
    cxp
    #
    cfv
    #
    cc0
    @9
    cM
    cA
    @13
    @9
    cF
    ccoe
    cfv
    c0p
    ccoe
    cfv
    #
    cA
    @13
    @9
    cF
    c0p
    ccoe
    @12
    fveq2d
    dgreq0.2
    @15
    @13
    coe0
    eqcomi
    3eqtr4g
    fveq1d
    @1
    @14
    cc0
    wceq
    @0
    @3
    cn0
    cc0
    cM
    c0ex
    fvconst2
    ad2antlr
    eqtrd
    jca
    @2
    @4
    wa
    @5
    @7
    @2
    @4
    @5
    @0
    cN
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @4
    @5
    wi
    @1
    @0
    cN
    @0
    cN
    @10
    cn0
    dgreq0.1
    cS
    cF
    dgrcl
    syl5eqel
    nn0red
    #
    cM
    nn0re
    #
    cN
    cM
    ltle
    syl2an
    imp
    @2
    @4
    @7
    @2
    @4
    @6
    cc0
    @2
    @6
    cc0
    wne
    #
    cM
    cN
    cle
    wbr
    #
    @4
    wn
    #
    @0
    @1
    @20
    @21
    cA
    cS
    cF
    cM
    cN
    dgreq0.2
    dgreq0.1
    dgrub
    3expia
    @1
    @17
    @16
    @21
    @22
    wb
    @0
    @19
    @18
    cM
    cN
    lenlt
    syl2anr
    sylibd
    necon4ad
    imp
    jca
    jaodan
    @2
    @8
    wa
    #
    @4
    @3
    @23
    @4
    cN
    cM
    wceq
    #
    wo
    #
    @4
    @3
    wo
    @2
    @5
    @25
    @7
    @2
    @5
    @25
    @0
    @16
    @17
    @5
    @25
    wb
    @1
    @18
    @19
    cN
    cM
    leloe
    syl2an
    biimpa
    adantrr
    @23
    @24
    @3
    @4
    @24
    @3
    @23
    cN
    cA
    cfv
    #
    @6
    wceq
    #
    cN
    cM
    cA
    fveq2
    @23
    @3
    @26
    cc0
    wceq
    #
    @27
    @0
    @3
    @28
    wb
    @1
    @8
    cA
    cS
    cF
    cN
    dgreq0.1
    dgreq0.2
    dgreq0
    ad2antrr
    @23
    @6
    cc0
    @26
    @2
    @5
    @7
    simprr
    eqeq2d
    bitr4d
    syl5ibr
    orim2d
    mpd
    orcomd
    impbida
end
