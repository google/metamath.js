include "com.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "fin23lem26.mm"
include "ensym.mm"
include "entr.mm"
include "sylan2.mm"
include "wo.mm"
include "wb.mm"
include "simpl.mm"
include "simprl.mm"
include "sseldd.mm"
include "nnfi.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "syl.mm"
include "simprr.mm"
include "word.mm"
include "nnord.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "ssrin.mm"
include "orim12i.mm"
include "fin23lem25.mm"
include "syl3anc.mm"
include "ordom.mm"
include "fin23lem24.mm"
include "mpanl1.mm"
include "bitrd.mm"
include "syl5ib.mm"
include "ralrimivva.mm"
include "ad2antrr.mm"
include "ineq1.mm"
include "breq1d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem fin23lem23
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let cC: class C

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
  assert |- ( ( ( S C_ _om /\ -. S e. Fin ) /\ i e. _om ) -> E! j e. S ( j i^i S ) ~~ i )

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
    vi
    cv
    #
    com
    wcel
    #
    wa
    vj
    cv
    #
    cS
    cin
    #
    @2
    cen
    wbr
    #
    vj
    cS
    wrex
    @6
    va
    cv
    #
    cS
    cin
    #
    @2
    cen
    wbr
    #
    wa
    #
    @4
    @7
    wceq
    #
    wi
    #
    va
    cS
    wral
    vj
    cS
    wral
    #
    @6
    vj
    cS
    wreu
    cS
    vi
    vj
    fin23lem26
    @0
    @13
    @1
    @3
    @0
    @12
    vj
    va
    cS
    cS
    @10
    @5
    @8
    cen
    wbr
    #
    @0
    @4
    cS
    wcel
    #
    @7
    cS
    wcel
    #
    wa
    #
    wa
    #
    @11
    @9
    @6
    @2
    @8
    cen
    wbr
    @14
    @8
    @2
    ensym
    @5
    @2
    @8
    entr
    sylan2
    @18
    @14
    @5
    @8
    wceq
    #
    @11
    @18
    @5
    cfn
    wcel
    #
    @8
    cfn
    wcel
    #
    @5
    @8
    wss
    #
    @8
    @5
    wss
    #
    wo
    #
    @14
    @19
    wb
    @18
    @4
    com
    wcel
    #
    @20
    @18
    cS
    com
    @4
    @0
    @17
    simpl
    #
    @0
    @15
    @16
    simprl
    sseldd
    #
    @25
    @4
    cfn
    wcel
    @5
    @4
    wss
    @20
    @4
    nnfi
    @4
    cS
    inss1
    @4
    @5
    ssfi
    sylancl
    syl
    @18
    @7
    com
    wcel
    #
    @21
    @18
    cS
    com
    @7
    @26
    @0
    @15
    @16
    simprr
    sseldd
    #
    @28
    @7
    cfn
    wcel
    @8
    @7
    wss
    @21
    @7
    nnfi
    @7
    cS
    inss1
    @7
    @8
    ssfi
    sylancl
    syl
    @18
    @4
    @7
    wss
    #
    @7
    @4
    wss
    #
    wo
    #
    @24
    @18
    @25
    @28
    @32
    @27
    @29
    @25
    @4
    word
    @7
    word
    @32
    @28
    @4
    nnord
    @7
    nnord
    @4
    @7
    ordtri2or2
    syl2an
    syl2anc
    @30
    @22
    @31
    @23
    @4
    @7
    cS
    ssrin
    @7
    @4
    cS
    ssrin
    orim12i
    syl
    @5
    @8
    fin23lem25
    syl3anc
    com
    word
    @0
    @17
    @19
    @11
    wb
    ordom
    com
    cS
    @4
    @7
    fin23lem24
    mpanl1
    bitrd
    syl5ib
    ralrimivva
    ad2antrr
    @6
    @9
    vj
    va
    cS
    @11
    @5
    @8
    @2
    cen
    @4
    @7
    cS
    ineq1
    breq1d
    reu4
    sylanbrc
end
