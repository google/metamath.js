include "clmod.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "cpw.mm"
include "clininds.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "lmodsn0.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "eqneqall.mm"
include "com12.mm"
include "syl5bi.mm"
include "syl.mm"
include "adantr.mm"
include "c0g.mm"
include "csn.mm"
include "crg.mm"
include "lmodring.mm"
include "eqid.mm"
include "0ring.mm"
include "sylan.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "co.mm"
include "wral.mm"
include "cmap.mm"
include "simpr.mm"
include "adantl.mm"
include "wf.mm"
include "snex.mm"
include "jctil.mm"
include "elmapg.mm"
include "cmpt.mm"
include "cxp.mm"
include "fconst2.mm"
include "fconstmpt.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "eqidd.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "ralrimiva.mm"
include "a1d.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "simpl.mm"
include "ancomd.mm"
include "islininds.mm"
include "mpbir2and.mm"
include "mpancom.mm"
include "expcom.mm"
include "jaoi.mm"
include "expd.mm"
include "3imp.mm"

theorem lindsrng01
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cM: class M
  let vf: setvar f
  let vv: setvar v
  let vx: setvar x
  let vk: setvar k
  assume lindsrng01.b: |- B = ( Base ` M )
  assume lindsrng01.r: |- R = ( Scalar ` M )
  assume lindsrng01.e: |- E = ( Base ` R )


  assert |- ( ( M e. LMod /\ ( ( # ` E ) = 0 \/ ( # ` E ) = 1 ) /\ S e. ~P B ) -> S linIndS M )

  proof
    cM
    clmod
    wcel
    #
    cE
    chash
    cfv
    #
    cc0
    wceq
    #
    @1
    c1
    wceq
    #
    wo
    #
    cS
    cB
    cpw
    #
    wcel
    #
    cS
    cM
    clininds
    wbr
    #
    @4
    @0
    @6
    @7
    wi
    @4
    @0
    @6
    @7
    @2
    @0
    @6
    wa
    #
    @7
    wi
    @3
    @8
    @2
    @7
    @0
    @2
    @7
    wi
    #
    @6
    @0
    cE
    c0
    wne
    #
    @9
    cE
    cR
    cM
    lindsrng01.r
    lindsrng01.e
    lmodsn0
    @2
    cE
    c0
    wceq
    #
    @10
    @7
    cE
    cvv
    wcel
    @2
    @11
    wb
    cE
    cR
    cbs
    cfv
    cvv
    lindsrng01.e
    cR
    cbs
    fvex
    eqeltri
    cE
    cvv
    hasheq0
    ax-mp
    @11
    @10
    @7
    @7
    cE
    c0
    eqneqall
    com12
    syl5bi
    syl
    adantr
    com12
    @8
    @3
    @7
    cE
    cR
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @8
    @3
    wa
    #
    @7
    @8
    cR
    crg
    wcel
    #
    @3
    @14
    @0
    @16
    @6
    cR
    cM
    lindsrng01.r
    lmodring
    adantr
    cE
    cR
    @12
    lindsrng01.e
    @12
    eqid
    #
    0ring
    sylan
    @14
    @15
    wa
    #
    @7
    @6
    vf
    cv
    #
    @12
    cfsupp
    wbr
    #
    @19
    cS
    cM
    clinc
    cfv
    #
    co
    #
    cM
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    vv
    cv
    #
    @19
    cfv
    #
    @12
    wceq
    #
    vv
    cS
    wral
    #
    wi
    #
    vf
    cE
    cS
    cmap
    co
    #
    wral
    #
    @15
    @6
    @14
    @8
    @6
    @3
    @0
    @6
    simpr
    adantr
    #
    adantl
    @18
    @32
    @30
    vf
    @13
    cS
    cmap
    co
    #
    wral
    #
    @18
    @30
    vf
    @34
    @18
    @19
    @34
    wcel
    #
    cS
    @13
    @19
    wf
    #
    @30
    @18
    @13
    cvv
    wcel
    #
    @6
    wa
    #
    @36
    @37
    wb
    @15
    @39
    @14
    @15
    @6
    @38
    @33
    @12
    snex
    jctil
    adantl
    @13
    cS
    @19
    cvv
    @5
    elmapg
    syl
    @37
    @19
    vx
    cS
    @12
    cmpt
    #
    wceq
    #
    @18
    @30
    @37
    @19
    cS
    @13
    cxp
    #
    wceq
    @41
    cS
    @12
    @19
    cR
    c0g
    fvex
    fconst2
    @42
    @40
    @19
    vx
    cS
    @12
    fconstmpt
    eqeq2i
    bitri
    @18
    @30
    @41
    @40
    @12
    cfsupp
    wbr
    #
    @40
    cS
    @21
    co
    #
    @23
    wceq
    #
    wa
    #
    @26
    @40
    cfv
    #
    @12
    wceq
    #
    vv
    cS
    wral
    #
    wi
    @18
    @49
    @46
    @18
    @48
    vv
    cS
    @18
    @26
    cS
    wcel
    #
    wa
    #
    vx
    @26
    @12
    @12
    cS
    @40
    cvv
    @51
    @40
    eqidd
    @51
    vx
    cv
    @26
    wceq
    wa
    @12
    eqidd
    @18
    @50
    simpr
    @51
    cR
    c0g
    fvexd
    fvmptd
    ralrimiva
    a1d
    @41
    @25
    @46
    @29
    @49
    @41
    @20
    @43
    @24
    @45
    @19
    @40
    @12
    cfsupp
    breq1
    @41
    @22
    @44
    @23
    @19
    @40
    cS
    @21
    oveq1
    eqeq1d
    anbi12d
    @41
    @28
    @48
    vv
    cS
    @41
    @27
    @47
    @12
    @26
    @19
    @40
    fveq1
    eqeq1d
    ralbidv
    imbi12d
    syl5ibrcom
    syl5bi
    sylbid
    ralrimiv
    @14
    @32
    @35
    wb
    @15
    @14
    @30
    vf
    @31
    @34
    cE
    @13
    cS
    cmap
    oveq1
    raleqdv
    adantr
    mpbird
    @18
    @6
    @0
    wa
    #
    @7
    @6
    @32
    wa
    wb
    @15
    @52
    @14
    @15
    @0
    @6
    @8
    @3
    simpl
    ancomd
    adantl
    vv
    cB
    cR
    cS
    vf
    cE
    cM
    @5
    clmod
    @12
    @23
    lindsrng01.b
    @23
    eqid
    lindsrng01.r
    lindsrng01.e
    @17
    islininds
    syl
    mpbir2and
    mpancom
    expcom
    jaoi
    expd
    com12
    3imp
end
