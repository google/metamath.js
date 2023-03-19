include "c0.mm"
include "wne.mm"
include "wer.mm"
include "wral.mm"
include "wa.mm"
include "ciin.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "wrex.mm"
include "r19.2z.mm"
include "errel.mm"
include "df-rel.mm"
include "sylib.mm"
include "reximi.mm"
include "iinss.mm"
include "3syl.mm"
include "sylibr.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "id.mm"
include "ersymb.mm"
include "biimpd.mm"
include "df-br.mm"
include "3imtr3g.mm"
include "ral2imi.mm"
include "adantl.mm"
include "wb.mm"
include "opex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "bitri.mm"
include "3imtr4g.mm"
include "imp.mm"
include "r19.26.mm"
include "ertr.mm"
include "anbi12i.mm"
include "syl5bir.mm"
include "simpl.mm"
include "simpr.mm"
include "erref.mm"
include "expcom.mm"
include "ralimdv.mm"
include "com12.mm"
include "cdm.mm"
include "vex.mm"
include "opeldm.mm"
include "erdm.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "sylan2.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "expdimp.mm"
include "impbid.mm"
include "syl6bbr.mm"
include "iserd.mm"

theorem iiner
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint R u
  disjoint R v
  disjoint R w
  assert |- ( ( A =/= (/) /\ A. x e. A R Er B ) -> |^|_ x e. A R Er B )

  proof
    cA
    c0
    wne
    #
    cB
    cR
    wer
    #
    vx
    cA
    wral
    #
    wa
    #
    vu
    vv
    vw
    cB
    vx
    cA
    cR
    ciin
    #
    @3
    @4
    cvv
    cvv
    cxp
    #
    wss
    #
    @4
    wrel
    @3
    @1
    vx
    cA
    wrex
    cR
    @5
    wss
    #
    vx
    cA
    wrex
    @6
    @1
    vx
    cA
    r19.2z
    @1
    @7
    vx
    cA
    @1
    cR
    wrel
    @7
    cB
    cR
    errel
    cR
    df-rel
    sylib
    reximi
    vx
    cA
    cR
    @5
    iinss
    3syl
    @4
    df-rel
    sylibr
    @3
    vu
    cv
    #
    vv
    cv
    #
    @4
    wbr
    #
    @9
    @8
    @4
    wbr
    #
    @3
    @8
    @9
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    @9
    @8
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    @10
    @11
    @2
    @14
    @17
    wi
    @0
    @1
    @13
    @16
    vx
    cA
    @1
    @8
    @9
    cR
    wbr
    #
    @9
    @8
    cR
    wbr
    #
    @13
    @16
    @1
    @18
    @19
    @1
    @8
    @9
    cR
    cB
    @1
    id
    #
    ersymb
    biimpd
    @8
    @9
    cR
    df-br
    #
    @9
    @8
    cR
    df-br
    3imtr3g
    ral2imi
    adantl
    @10
    @12
    @4
    wcel
    #
    @14
    @8
    @9
    @4
    df-br
    @12
    cvv
    wcel
    @22
    @14
    wb
    @8
    @9
    opex
    vx
    @12
    cA
    cR
    cvv
    eliin
    ax-mp
    bitri
    #
    @11
    @15
    @4
    wcel
    #
    @17
    @9
    @8
    @4
    df-br
    @15
    cvv
    wcel
    @24
    @17
    wb
    @9
    @8
    opex
    vx
    @15
    cA
    cR
    cvv
    eliin
    ax-mp
    bitri
    3imtr4g
    imp
    @3
    @10
    @9
    vw
    cv
    #
    @4
    wbr
    #
    wa
    #
    @8
    @25
    @4
    wbr
    #
    @3
    @14
    @9
    @25
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @8
    @25
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    @27
    @28
    @32
    @13
    @30
    wa
    #
    vx
    cA
    wral
    #
    @3
    @35
    @13
    @30
    vx
    cA
    r19.26
    @2
    @37
    @35
    wi
    @0
    @1
    @36
    @34
    vx
    cA
    @1
    @18
    @9
    @25
    cR
    wbr
    #
    wa
    @8
    @25
    cR
    wbr
    @36
    @34
    @1
    @8
    @9
    @25
    cR
    cB
    @20
    ertr
    @18
    @13
    @38
    @30
    @21
    @9
    @25
    cR
    df-br
    anbi12i
    @8
    @25
    cR
    df-br
    3imtr3g
    ral2imi
    adantl
    syl5bir
    @10
    @14
    @26
    @31
    @23
    @26
    @29
    @4
    wcel
    #
    @31
    @9
    @25
    @4
    df-br
    @29
    cvv
    wcel
    @39
    @31
    wb
    @9
    @25
    opex
    vx
    @29
    cA
    cR
    cvv
    eliin
    ax-mp
    bitri
    anbi12i
    @28
    @33
    @4
    wcel
    #
    @35
    @8
    @25
    @4
    df-br
    @33
    cvv
    wcel
    @40
    @35
    wb
    @8
    @25
    opex
    vx
    @33
    cA
    cR
    cvv
    eliin
    ax-mp
    bitri
    3imtr4g
    imp
    @3
    @8
    cB
    wcel
    #
    @8
    @8
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    @8
    @8
    @4
    wbr
    #
    @3
    @41
    @44
    @2
    @41
    @44
    wi
    @0
    @41
    @2
    @44
    @41
    @1
    @43
    vx
    cA
    @1
    @41
    @43
    @1
    @41
    wa
    #
    @8
    @8
    cR
    wbr
    @43
    @46
    @8
    cR
    cB
    @1
    @41
    simpl
    @1
    @41
    simpr
    erref
    @8
    @8
    cR
    df-br
    sylib
    expcom
    ralimdv
    com12
    adantl
    @0
    @2
    @44
    @41
    @2
    @44
    wa
    @1
    @43
    wa
    #
    vx
    cA
    wral
    #
    @0
    @41
    @1
    @43
    vx
    cA
    r19.26
    @0
    @48
    @41
    @0
    @48
    wa
    @47
    vx
    cA
    wrex
    @41
    @47
    vx
    cA
    r19.2z
    @47
    @41
    vx
    cA
    @43
    @1
    @8
    cR
    cdm
    #
    wcel
    #
    @41
    @8
    @8
    cR
    vu
    vex
    #
    @51
    opeldm
    @1
    @50
    @41
    @1
    @49
    cB
    @8
    cB
    cR
    erdm
    eleq2d
    biimpa
    sylan2
    rexlimivw
    syl
    ex
    syl5bir
    expdimp
    impbid
    @45
    @42
    @4
    wcel
    #
    @44
    @8
    @8
    @4
    df-br
    @42
    cvv
    wcel
    @52
    @44
    wb
    @8
    @8
    opex
    vx
    @42
    cA
    cR
    cvv
    eliin
    ax-mp
    bitri
    syl6bbr
    iserd
end
