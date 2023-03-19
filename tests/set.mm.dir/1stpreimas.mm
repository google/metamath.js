include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cres.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cxp.mm"
include "cv.mm"
include "cvv.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "cop.mm"
include "1st2ndb.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "fvex.mm"
include "elsn.mm"
include "adantl.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "simplr.mm"
include "simprrr.mm"
include "elimasng.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "eqeltrd.mm"
include "fvres.mm"
include "syl.mm"
include "jca.mm"
include "wss.mm"
include "df-rel.mm"
include "adantr.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "sylibr.mm"
include "wex.mm"
include "wrex.mm"
include "eqeltrrd.mm"
include "simpr.mm"
include "eleq1d.mm"
include "1st2nd.mm"
include "ad2ant2r.mm"
include "simprl.mm"
include "rspcedvd.mm"
include "df-rex.mm"
include "sylib.mm"
include "elima3.mm"
include "impbida.mm"
include "wb.mm"
include "elxp7.mm"
include "a1i.mm"
include "wfn.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "ssv.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fniniseg.mm"
include "3bitr4rd.mm"
include "eqrdv.mm"

theorem 1stpreimas
  let cA: class A
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vz: setvar z


  assert |- ( ( Rel A /\ X e. V ) -> ( `' ( 1st |` A ) " { X } ) = ( { X } X. ( A " { X } ) ) )

  proof
    cA
    wrel
    #
    cX
    cV
    wcel
    #
    wa
    #
    vz
    c1st
    cA
    cres
    #
    ccnv
    cX
    csn
    #
    cima
    #
    @4
    cA
    @4
    cima
    #
    cxp
    #
    @2
    vz
    cv
    #
    cvv
    cvv
    cxp
    #
    wcel
    #
    @8
    c1st
    cfv
    #
    @4
    wcel
    #
    @8
    c2nd
    cfv
    #
    @6
    wcel
    #
    wa
    #
    wa
    #
    @8
    cA
    wcel
    #
    @8
    @3
    cfv
    #
    cX
    wceq
    #
    wa
    #
    @8
    @7
    wcel
    #
    @8
    @5
    wcel
    #
    @2
    @16
    @20
    @2
    @16
    wa
    #
    @17
    @19
    @23
    @8
    cX
    @13
    cop
    #
    cA
    @23
    @8
    @11
    @13
    cop
    #
    @24
    @10
    @8
    @25
    wceq
    #
    @2
    @15
    @10
    @26
    @8
    1st2ndb
    biimpi
    ad2antrl
    @23
    @11
    cX
    @13
    @16
    @11
    cX
    wceq
    #
    @2
    @12
    @27
    @10
    @14
    @12
    @27
    @11
    cX
    @8
    c1st
    fvex
    elsn
    #
    biimpi
    ad2antrl
    adantl
    #
    opeq1d
    eqtrd
    @23
    @1
    @14
    @14
    @24
    cA
    wcel
    #
    @0
    @1
    @16
    simplr
    @2
    @10
    @12
    @14
    simprrr
    #
    @31
    @1
    @14
    wa
    @14
    @30
    cA
    cX
    @13
    cV
    @6
    elimasng
    biimpa
    syl21anc
    eqeltrd
    #
    @23
    @18
    @11
    cX
    @23
    @17
    @18
    @11
    wceq
    #
    @32
    @8
    cA
    c1st
    fvres
    #
    syl
    @29
    eqtrd
    jca
    @2
    @20
    wa
    #
    @10
    @15
    @2
    @17
    @10
    @19
    @2
    cA
    @9
    @8
    @0
    cA
    @9
    wss
    #
    @1
    @0
    @36
    cA
    df-rel
    biimpi
    adantr
    sselda
    adantrr
    @35
    @12
    @14
    @35
    @27
    @12
    @35
    @18
    @11
    cX
    @17
    @33
    @2
    @19
    @34
    ad2antrl
    @2
    @17
    @19
    simprr
    eqtr3d
    #
    @28
    sylibr
    #
    @35
    vx
    cv
    #
    @4
    wcel
    @39
    @13
    cop
    #
    cA
    wcel
    #
    wa
    vx
    wex
    #
    @14
    @35
    @41
    vx
    @4
    wrex
    @42
    @35
    @41
    @30
    vx
    cX
    @4
    @35
    @11
    cX
    @4
    @37
    @38
    eqeltrrd
    @35
    @39
    cX
    wceq
    #
    wa
    #
    @40
    @24
    cA
    @44
    @39
    cX
    @13
    @35
    @43
    simpr
    opeq1d
    eleq1d
    @35
    @8
    @24
    cA
    @35
    @8
    @25
    @24
    @0
    @17
    @26
    @1
    @19
    @8
    cA
    1st2nd
    ad2ant2r
    @35
    @11
    cX
    @13
    @37
    opeq1d
    eqtrd
    @2
    @17
    @19
    simprl
    eqeltrrd
    rspcedvd
    @41
    vx
    @4
    df-rex
    sylib
    vx
    @13
    cA
    @4
    @8
    c2nd
    fvex
    elima3
    sylibr
    jca
    jca
    impbida
    @21
    @16
    wb
    @2
    @8
    @4
    @6
    elxp7
    a1i
    @22
    @20
    wb
    #
    @2
    @3
    cA
    wfn
    #
    @45
    c1st
    cvv
    wfn
    #
    cA
    cvv
    wss
    @46
    cvv
    cvv
    c1st
    wfo
    @47
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    cA
    ssv
    cvv
    cA
    c1st
    fnssres
    mp2an
    cA
    cX
    @8
    @3
    fniniseg
    ax-mp
    a1i
    3bitr4rd
    eqrdv
end
