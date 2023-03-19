include "wcel.mm"
include "cvv.mm"
include "ctpos.mm"
include "wbr.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "wa.mm"
include "wi.mm"
include "reltpos.mm"
include "brrelexi.mm"
include "a1i.mm"
include "elex.mm"
include "adantr.mm"
include "wb.mm"
include "cv.mm"
include "cmpt.mm"
include "wex.mm"
include "ccom.mm"
include "df-tpos.mm"
include "breqi.mm"
include "brcog.mm"
include "syl5bb.mm"
include "wceq.mm"
include "cfv.mm"
include "wfun.mm"
include "funmpt.mm"
include "funbrfv2b.mm"
include "ax-mp.mm"
include "snex.mm"
include "cnvex.mm"
include "uniex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "sneq.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "fvmpt.mm"
include "eqeq2d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "ancom.mm"
include "anbi1i.mm"
include "anass.mm"
include "exbii.mm"
include "breq1.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "syl6bb.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem brtpos2
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( B e. V -> ( A tpos F B <-> ( A e. ( `' dom F u. { (/) } ) /\ U. `' { A } F B ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    cF
    ctpos
    #
    wbr
    #
    cA
    cF
    cdm
    ccnv
    c0
    csn
    cun
    #
    wcel
    #
    cA
    csn
    #
    ccnv
    #
    cuni
    #
    cB
    cF
    wbr
    #
    wa
    #
    @3
    @1
    wi
    @0
    cA
    cB
    @2
    cF
    reltpos
    brrelexi
    a1i
    @10
    @1
    wi
    @0
    @5
    @1
    @9
    cA
    @4
    elex
    adantr
    a1i
    @1
    @0
    @3
    @10
    wb
    @1
    @0
    wa
    #
    @3
    cA
    vy
    cv
    #
    vx
    @4
    vx
    cv
    #
    csn
    #
    ccnv
    #
    cuni
    #
    cmpt
    #
    wbr
    #
    @12
    cB
    cF
    wbr
    #
    wa
    #
    vy
    wex
    #
    @10
    @3
    cA
    cB
    cF
    @17
    ccom
    #
    wbr
    @11
    @21
    cA
    cB
    @2
    @22
    vx
    cF
    df-tpos
    breqi
    vy
    cA
    cB
    cF
    @17
    cvv
    cV
    brcog
    syl5bb
    @21
    @12
    @8
    wceq
    #
    @5
    @19
    wa
    #
    wa
    #
    vy
    wex
    @10
    @20
    @25
    vy
    @20
    @23
    @5
    wa
    #
    @19
    wa
    @25
    @18
    @26
    @19
    @18
    @5
    @23
    wa
    #
    @26
    @18
    cA
    @17
    cdm
    #
    wcel
    #
    cA
    @17
    cfv
    #
    @12
    wceq
    #
    wa
    #
    @27
    @17
    wfun
    @18
    @32
    wb
    vx
    @4
    @16
    funmpt
    cA
    @12
    @17
    funbrfv2b
    ax-mp
    @32
    @5
    @12
    @30
    wceq
    #
    wa
    @27
    @29
    @5
    @31
    @33
    @28
    @4
    cA
    vx
    @4
    @16
    @17
    @15
    @14
    @13
    snex
    cnvex
    uniex
    @17
    eqid
    #
    dmmpti
    eleq2i
    @30
    @12
    eqcom
    anbi12i
    @5
    @33
    @23
    @5
    @30
    @8
    @12
    vx
    cA
    @16
    @8
    @4
    @17
    @13
    cA
    wceq
    #
    @15
    @7
    @35
    @14
    @6
    @13
    cA
    sneq
    cnveqd
    unieqd
    @34
    @7
    @6
    cA
    snex
    cnvex
    uniex
    #
    fvmpt
    eqeq2d
    pm5.32i
    bitri
    bitri
    @5
    @23
    ancom
    bitri
    anbi1i
    @23
    @5
    @19
    anass
    bitri
    exbii
    @24
    @10
    vy
    @8
    @36
    @23
    @19
    @9
    @5
    @12
    @8
    cB
    cF
    breq1
    anbi2d
    ceqsexv
    bitri
    syl6bb
    expcom
    pm5.21ndd
end
