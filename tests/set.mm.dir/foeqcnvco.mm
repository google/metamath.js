include "wfo.mm"
include "wa.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wi.mm"
include "fococnv2.mm"
include "cnveq.mm"
include "coeq2d.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "adantr.mm"
include "wfn.mm"
include "fofn.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cop.mm"
include "adantl.mm"
include "fnopfv.mm"
include "sylan.mm"
include "fvex.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitri.mm"
include "sylibr.mm"
include "weq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "brco.mm"
include "adantlr.mm"
include "wb.mm"
include "breq.mm"
include "mpbid.mm"
include "wf.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "resieq.mm"
include "eqcomd.mm"
include "eqfnfvd.mm"
include "ex.mm"
include "impbid.mm"

theorem foeqcnvco
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : A -onto-> B /\ G : A -onto-> B ) -> ( F = G <-> ( F o. `' G ) = ( _I |` B ) ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cG
    wfo
    #
    wa
    #
    cF
    cG
    wceq
    #
    cF
    cG
    ccnv
    #
    ccom
    #
    cid
    cB
    cres
    #
    wceq
    #
    @0
    @3
    @7
    wi
    @1
    @0
    cF
    cF
    ccnv
    #
    ccom
    #
    @6
    wceq
    @3
    @7
    cA
    cB
    cF
    fococnv2
    @3
    @9
    @5
    @6
    @3
    @8
    @4
    cF
    cF
    cG
    cnveq
    coeq2d
    eqeq1d
    syl5ibcom
    adantr
    @2
    @7
    @3
    @2
    @7
    wa
    #
    vx
    cA
    cF
    cG
    @0
    cF
    cA
    wfn
    #
    @1
    @7
    cA
    cB
    cF
    fofn
    #
    ad2antrr
    @1
    cG
    cA
    wfn
    #
    @0
    @7
    cA
    cB
    cG
    fofn
    #
    ad2antlr
    @10
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @15
    cG
    cfv
    #
    @15
    cF
    cfv
    #
    @17
    @18
    @19
    @6
    wbr
    #
    @18
    @19
    wceq
    #
    @17
    @18
    @19
    @5
    wbr
    #
    @20
    @2
    @16
    @22
    @7
    @2
    @16
    wa
    #
    @18
    vy
    cv
    #
    @4
    wbr
    #
    @24
    @19
    cF
    wbr
    #
    wa
    #
    vy
    wex
    #
    @22
    @23
    @18
    @15
    @4
    wbr
    #
    @15
    @19
    cF
    wbr
    #
    @28
    @23
    @15
    @18
    cop
    cG
    wcel
    #
    @29
    @2
    @13
    @16
    @31
    @1
    @13
    @0
    @14
    adantl
    cA
    @15
    cG
    fnopfv
    sylan
    @29
    @15
    @18
    cG
    wbr
    @31
    @18
    @15
    cG
    @15
    cG
    fvex
    #
    vx
    vex
    #
    brcnv
    @15
    @18
    cG
    df-br
    bitri
    sylibr
    @23
    @15
    @19
    cop
    cF
    wcel
    #
    @30
    @2
    @11
    @16
    @34
    @0
    @11
    @1
    @12
    adantr
    cA
    @15
    cF
    fnopfv
    sylan
    @15
    @19
    cF
    df-br
    sylibr
    @27
    @29
    @30
    wa
    vy
    @15
    @33
    vy
    vx
    weq
    @25
    @29
    @26
    @30
    @24
    @15
    @18
    @4
    breq2
    @24
    @15
    @19
    cF
    breq1
    anbi12d
    spcev
    syl2anc
    vy
    @18
    @19
    cF
    @4
    @32
    @15
    cF
    fvex
    brco
    sylibr
    adantlr
    @7
    @22
    @20
    wb
    @2
    @16
    @18
    @19
    @5
    @6
    breq
    ad2antlr
    mpbid
    @2
    @16
    @20
    @21
    wb
    #
    @7
    @23
    @18
    cB
    wcel
    @19
    cB
    wcel
    @35
    @2
    cA
    cB
    @15
    cG
    @1
    cA
    cB
    cG
    wf
    @0
    cA
    cB
    cG
    fof
    adantl
    ffvelrnda
    @2
    cA
    cB
    @15
    cF
    @0
    cA
    cB
    cF
    wf
    @1
    cA
    cB
    cF
    fof
    adantr
    ffvelrnda
    cB
    @18
    @19
    resieq
    syl2anc
    adantlr
    mpbid
    eqcomd
    eqfnfvd
    ex
    impbid
end
