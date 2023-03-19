include "com.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cep.mm"
include "wor.mm"
include "wpo.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wiso.mm"
include "word.mm"
include "wwe.mm"
include "ordom.mm"
include "ordwe.mm"
include "weso.mm"
include "mp2b.mm"
include "a1i.mm"
include "sopo.mm"
include "ax-mp.mm"
include "poss.mm"
include "mpi.mm"
include "adantr.mm"
include "wf1o.mm"
include "fin23lem22.mm"
include "f1ofo.mm"
include "syl.mm"
include "cin.mm"
include "cen.mm"
include "crio.mm"
include "csdm.mm"
include "wb.mm"
include "nnsdomel.mm"
include "adantl.mm"
include "biimpd.mm"
include "wreu.mm"
include "fin23lem23.mm"
include "adantrr.mm"
include "wceq.mm"
include "ineq1.mm"
include "breq1d.mm"
include "cbvreuv.mm"
include "sylib.mm"
include "nfv.mm"
include "cbvriotav.mm"
include "riotaprop.mm"
include "simprd.mm"
include "simprr.mm"
include "adantrl.mm"
include "ensymd.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "ensdomtr.mm"
include "expr.mm"
include "con0.mm"
include "simpll.mm"
include "omsson.mm"
include "syl6ss.mm"
include "simpld.mm"
include "sseldd.mm"
include "onsdominel.mm"
include "3expia.mm"
include "3syld.mm"
include "simprl.mm"
include "breq2.mm"
include "riotabidv.mm"
include "fvmptg.mm"
include "eleq12d.mm"
include "sylibrd.mm"
include "epel.mm"
include "fvex.mm"
include "epelc.mm"
include "3imtr4g.mm"
include "ralrimivva.mm"
include "soisoi.mm"
include "syl22anc.mm"

theorem fin23lem27
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  assume fin23lem22.b: |- C = ( i e. _om |-> ( iota_ j e. S ( j i^i S ) ~~ i ) )

  disjoint i j
  disjoint S i
  disjoint S j
  disjoint a i
  disjoint b i
  disjoint a j
  disjoint b j
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint C a
  disjoint C b
  assert |- ( ( S C_ _om /\ -. S e. Fin ) -> C Isom _E , _E ( _om , S ) )

  proof
    cS
    com
    wss
    #
    cS
    cfn
    wcel
    wn
    #
    wa
    #
    com
    cep
    wor
    #
    cS
    cep
    wpo
    #
    com
    cS
    cC
    wfo
    #
    va
    cv
    #
    vb
    cv
    #
    cep
    wbr
    #
    @6
    cC
    cfv
    #
    @7
    cC
    cfv
    #
    cep
    wbr
    #
    wi
    #
    vb
    com
    wral
    va
    com
    wral
    com
    cS
    cep
    cep
    cC
    wiso
    @3
    @2
    com
    word
    com
    cep
    wwe
    @3
    ordom
    com
    ordwe
    com
    cep
    weso
    mp2b
    #
    a1i
    @0
    @4
    @1
    @0
    com
    cep
    wpo
    #
    @4
    @3
    @14
    @13
    com
    cep
    sopo
    ax-mp
    cS
    com
    cep
    poss
    mpi
    adantr
    @2
    com
    cS
    cC
    wf1o
    @5
    cC
    cS
    vi
    vj
    fin23lem22.b
    fin23lem22
    com
    cS
    cC
    f1ofo
    syl
    @2
    @12
    va
    vb
    com
    com
    @2
    @6
    com
    wcel
    #
    @7
    com
    wcel
    #
    wa
    #
    wa
    #
    @6
    @7
    wcel
    #
    @9
    @10
    wcel
    #
    @8
    @11
    @18
    @19
    vj
    cv
    #
    cS
    cin
    #
    @6
    cen
    wbr
    #
    vj
    cS
    crio
    #
    @22
    @7
    cen
    wbr
    #
    vj
    cS
    crio
    #
    wcel
    #
    @20
    @18
    @19
    @6
    @7
    csdm
    wbr
    #
    @24
    cS
    cin
    #
    @26
    cS
    cin
    #
    csdm
    wbr
    #
    @27
    @18
    @19
    @28
    @17
    @19
    @28
    wb
    @2
    @6
    @7
    nnsdomel
    adantl
    biimpd
    @2
    @17
    @28
    @31
    @2
    @17
    @28
    wa
    wa
    #
    @29
    @6
    cen
    wbr
    #
    @6
    @30
    csdm
    wbr
    #
    @31
    @2
    @17
    @33
    @28
    @18
    @24
    cS
    wcel
    #
    @33
    @18
    vi
    cv
    #
    cS
    cin
    #
    @6
    cen
    wbr
    #
    vi
    cS
    wreu
    #
    @35
    @33
    wa
    @18
    @23
    vj
    cS
    wreu
    #
    @39
    @2
    @15
    @40
    @16
    cS
    va
    vj
    fin23lem23
    adantrr
    @23
    @38
    vj
    vi
    cS
    @21
    @36
    wceq
    #
    @22
    @37
    @6
    cen
    @21
    @36
    cS
    ineq1
    #
    breq1d
    #
    cbvreuv
    sylib
    @38
    @33
    vi
    cS
    @24
    @33
    vi
    nfv
    @23
    @38
    vj
    vi
    cS
    @43
    cbvriotav
    @36
    @24
    wceq
    @37
    @29
    @6
    cen
    @36
    @24
    cS
    ineq1
    breq1d
    riotaprop
    syl
    #
    simprd
    adantrr
    @32
    @28
    @7
    @30
    cen
    wbr
    #
    @34
    @2
    @17
    @28
    simprr
    @2
    @17
    @45
    @28
    @18
    @30
    @7
    @18
    @26
    cS
    wcel
    #
    @30
    @7
    cen
    wbr
    #
    @18
    @37
    @7
    cen
    wbr
    #
    vi
    cS
    wreu
    #
    @46
    @47
    wa
    @18
    @25
    vj
    cS
    wreu
    #
    @49
    @2
    @16
    @50
    @15
    cS
    vb
    vj
    fin23lem23
    adantrl
    @25
    @48
    vj
    vi
    cS
    @41
    @22
    @37
    @7
    cen
    @42
    breq1d
    #
    cbvreuv
    sylib
    @48
    @47
    vi
    cS
    @26
    @47
    vi
    nfv
    @25
    @48
    vj
    vi
    cS
    @51
    cbvriotav
    @36
    @26
    wceq
    @37
    @30
    @7
    cen
    @36
    @26
    cS
    ineq1
    breq1d
    riotaprop
    syl
    #
    simprd
    ensymd
    adantrr
    @6
    @7
    @30
    sdomentr
    syl2anc
    @29
    @6
    @30
    ensdomtr
    syl2anc
    expr
    @18
    @24
    con0
    wcel
    #
    @26
    con0
    wcel
    #
    @31
    @27
    wi
    @18
    cS
    con0
    @24
    @18
    cS
    com
    con0
    @0
    @1
    @17
    simpll
    omsson
    syl6ss
    #
    @18
    @35
    @33
    @44
    simpld
    #
    sseldd
    @18
    cS
    con0
    @26
    @55
    @18
    @46
    @47
    @52
    simpld
    #
    sseldd
    @53
    @54
    @31
    @27
    @24
    @26
    cS
    onsdominel
    3expia
    syl2anc
    3syld
    @18
    @9
    @24
    @10
    @26
    @18
    @15
    @35
    @9
    @24
    wceq
    @2
    @15
    @16
    simprl
    @56
    vi
    @6
    @22
    @36
    cen
    wbr
    #
    vj
    cS
    crio
    #
    @24
    com
    cS
    cC
    @36
    @6
    wceq
    @58
    @23
    vj
    cS
    @36
    @6
    @22
    cen
    breq2
    riotabidv
    fin23lem22.b
    fvmptg
    syl2anc
    @18
    @16
    @46
    @10
    @26
    wceq
    @2
    @15
    @16
    simprr
    @57
    vi
    @7
    @59
    @26
    com
    cS
    cC
    @36
    @7
    wceq
    @58
    @25
    vj
    cS
    @36
    @7
    @22
    cen
    breq2
    riotabidv
    fin23lem22.b
    fvmptg
    syl2anc
    eleq12d
    sylibrd
    va
    vb
    epel
    @9
    @10
    @7
    cC
    fvex
    epelc
    3imtr4g
    ralrimivva
    va
    vb
    com
    cS
    cep
    cep
    cC
    soisoi
    syl22anc
end
