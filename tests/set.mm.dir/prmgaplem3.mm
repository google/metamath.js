include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "cprime.mm"
include "crab.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cn.mm"
include "prmssnn.mm"
include "nnssre.mm"
include "sstri.mm"
include "syl6ss.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "fzofi.mm"
include "wa.mm"
include "breq1.mm"
include "elrab.mm"
include "cn0.mm"
include "prmnn.mm"
include "nnnn0d.mm"
include "ad2antrl.mm"
include "eluzge3nn.mm"
include "adantr.mm"
include "simprr.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "sylancr.mm"
include "c2.mm"
include "2prm.mm"
include "cz.mm"
include "eluz2.mm"
include "c1.mm"
include "caddc.mm"
include "df-3.mm"
include "breq1i.mm"
include "wb.mm"
include "2z.mm"
include "zltp1le.mm"
include "mpan.mm"
include "biimprd.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "wceq.mm"
include "sseq1.mm"
include "eleq1.mm"
include "neeq1.mm"
include "3anbi123d.mm"
include "ax-mp.mm"
include "fimaxre.mm"

theorem prmgaplem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cN: class N
  let vp: setvar p
  let vi: setvar i
  assume prmgaplem3.a: |- A = { p e. Prime | p < N }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint N p
  disjoint N i
  disjoint i p
  assert |- ( N e. ( ZZ>= ` 3 ) -> E. x e. A A. y e. A y <_ x )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cA
    wrex
    @0
    vp
    cv
    #
    cN
    clt
    wbr
    #
    vp
    cprime
    crab
    #
    cr
    wss
    #
    @7
    cfn
    wcel
    #
    @7
    c0
    wne
    #
    @4
    @0
    @7
    cprime
    cr
    @7
    cprime
    wss
    @0
    @6
    vp
    cprime
    ssrab2
    a1i
    cprime
    cn
    cr
    prmssnn
    nnssre
    sstri
    syl6ss
    @0
    cc0
    cN
    cfzo
    co
    #
    cfn
    wcel
    @7
    @11
    wss
    @9
    cc0
    cN
    fzofi
    @0
    vi
    @7
    @11
    vi
    cv
    #
    @7
    wcel
    @12
    cprime
    wcel
    #
    @12
    cN
    clt
    wbr
    #
    wa
    #
    @0
    @12
    @11
    wcel
    #
    @6
    @14
    vp
    @12
    cprime
    @5
    @12
    cN
    clt
    breq1
    elrab
    @0
    @15
    @16
    @0
    @15
    wa
    @12
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @14
    @16
    @13
    @17
    @0
    @14
    @13
    @12
    @12
    prmnn
    nnnn0d
    ad2antrl
    @0
    @18
    @15
    cN
    eluzge3nn
    adantr
    @0
    @13
    @14
    simprr
    @12
    cN
    elfzo0
    syl3anbrc
    ex
    syl5bi
    ssrdv
    @11
    @7
    ssfi
    sylancr
    @0
    c2
    @7
    wcel
    #
    @10
    @0
    c2
    cprime
    wcel
    #
    c2
    cN
    clt
    wbr
    #
    @19
    @20
    @0
    2prm
    a1i
    @0
    c3
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    c3
    cN
    cle
    wbr
    #
    w3a
    @21
    c3
    cN
    eluz2
    @23
    @24
    @21
    @22
    @23
    @24
    @21
    @24
    c2
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @23
    @21
    c3
    @25
    cN
    cle
    df-3
    breq1i
    @23
    @21
    @26
    c2
    cz
    wcel
    @23
    @21
    @26
    wb
    2z
    c2
    cN
    zltp1le
    mpan
    biimprd
    syl5bi
    imp
    3adant1
    sylbi
    @6
    @21
    vp
    c2
    cprime
    @5
    c2
    cN
    clt
    breq1
    elrab
    sylanbrc
    @7
    c2
    ne0i
    syl
    cA
    @7
    wceq
    #
    @4
    @8
    @9
    @10
    w3a
    wb
    prmgaplem3.a
    @27
    @1
    @8
    @2
    @9
    @3
    @10
    cA
    @7
    cr
    sseq1
    cA
    @7
    cfn
    eleq1
    cA
    @7
    c0
    neeq1
    3anbi123d
    ax-mp
    syl3anbrc
    vx
    vy
    cA
    fimaxre
    syl
end
