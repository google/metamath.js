include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "saluni.mm"
include "wn.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "cpw.mm"
include "cvv.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "pwsal.mm"
include "ax-mp.mm"
include "cin.mm"
include "inss2.mm"
include "eqsstri.mm"
include "pm3.2i.mm"
include "sseq2.mm"
include "elrab.mm"
include "mpbir.mm"
include "intss1.mm"
include "unissi.mm"
include "unieqi.mm"
include "unipw.mm"
include "eqtri.mm"
include "sseqtri.mm"
include "wral.mm"
include "wrex.mm"
include "csn.mm"
include "biimpi.mm"
include "simprd.mm"
include "adantl.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdif.mm"
include "wo.mm"
include "c2.mm"
include "0red.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "unitssre.mm"
include "id.mm"
include "syl6eleq.mm"
include "sseldi.mm"
include "cxr.mm"
include "cle.mm"
include "rexrd.mm"
include "1re.mm"
include "rexri.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "iccleub.mm"
include "1le2.mm"
include "letrd.mm"
include "eliccd.mm"
include "syl6eleqr.mm"
include "snelpwi.mm"
include "syl.mm"
include "cfn.mm"
include "snfi.mm"
include "fict.mm"
include "orc.mm"
include "jca.mm"
include "wceq.mm"
include "breq1.mm"
include "difeq2.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "elrab2.mm"
include "sylibr.mm"
include "elind.mm"
include "eqcomi.mm"
include "eleqtrd.mm"
include "adantr.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "snex.mm"
include "elint2.mm"
include "snidg.mm"
include "eleq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eluni2.mm"
include "rgen.mm"
include "dfss3.mm"
include "eqssi.mm"
include "wtru.mm"
include "salexct.mm"
include "trud.mm"
include "inss1.mm"
include "sseli.mm"
include "salexct2.mm"
include "pm2.65i.mm"
include "eqneltri.mm"

theorem salgencntex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cZ: class Z
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  let vw: setvar w
  let vk: setvar k
  assume salgencntex.a: |- A = ( 0 [,] 2 )
  assume salgencntex.s: |- S = { x e. ~P A | ( x ~<_ _om \/ ( A \ x ) ~<_ _om ) }
  assume salgencntex.b: |- B = ( 0 [,] 1 )
  assume salgencntex.t: |- T = ~P B
  assume salgencntex.c: |- C = ( S i^i T )
  assume salgencntex.z: |- Z = |^| { s e. SAlg | C C_ s }

  disjoint A x
  disjoint B x
  disjoint C s
  disjoint S s
  disjoint S x
  disjoint T s
  disjoint B t
  disjoint B y
  disjoint t y
  disjoint x y
  disjoint C t
  disjoint s t
  disjoint Z w
  disjoint Z y
  disjoint w y
  disjoint k x
  assert |- -. Z e. SAlg

  proof
    cZ
    csalg
    wcel
    #
    cZ
    cuni
    #
    cZ
    wcel
    #
    cZ
    saluni
    @2
    wn
    @0
    @1
    cB
    cZ
    @1
    cB
    @1
    cT
    cuni
    #
    cB
    cZ
    cT
    cZ
    cC
    vs
    cv
    #
    wss
    #
    vs
    csalg
    crab
    #
    cint
    #
    cT
    salgencntex.z
    cT
    @6
    wcel
    #
    @7
    cT
    wss
    @8
    cT
    csalg
    wcel
    #
    cC
    cT
    wss
    #
    wa
    @9
    @10
    cT
    cB
    cpw
    #
    csalg
    salgencntex.t
    cB
    cvv
    wcel
    @11
    csalg
    wcel
    cB
    cc0
    c1
    cicc
    co
    #
    cvv
    salgencntex.b
    cc0
    c1
    cicc
    ovex
    eqeltri
    cvv
    cB
    pwsal
    ax-mp
    eqeltri
    cC
    cS
    cT
    cin
    #
    cT
    salgencntex.c
    cS
    cT
    inss2
    eqsstri
    pm3.2i
    @5
    @10
    vs
    cT
    csalg
    @4
    cT
    cC
    sseq2
    elrab
    mpbir
    cT
    @6
    intss1
    ax-mp
    eqsstri
    unissi
    @3
    @11
    cuni
    cB
    cT
    @11
    salgencntex.t
    unieqi
    cB
    unipw
    eqtri
    sseqtri
    cB
    @1
    wss
    vy
    cv
    #
    @1
    wcel
    #
    vy
    cB
    wral
    @15
    vy
    cB
    @14
    cB
    wcel
    #
    @14
    vw
    cv
    #
    wcel
    #
    vw
    cZ
    wrex
    #
    @15
    @16
    @14
    csn
    #
    cZ
    wcel
    @14
    @20
    wcel
    #
    @19
    @16
    @20
    @7
    cZ
    @16
    @20
    vt
    cv
    #
    wcel
    #
    vt
    @6
    wral
    @20
    @7
    wcel
    @16
    @23
    vt
    @6
    @16
    @22
    @6
    wcel
    #
    wa
    cC
    @22
    @20
    @24
    cC
    @22
    wss
    #
    @16
    @24
    @22
    csalg
    wcel
    #
    @25
    @24
    @26
    @25
    wa
    @5
    @25
    vs
    @22
    csalg
    @4
    @22
    cC
    sseq2
    elrab
    biimpi
    simprd
    adantl
    @16
    @20
    cC
    wcel
    @24
    @16
    @20
    @13
    cC
    @16
    cS
    cT
    @20
    @16
    @20
    cA
    cpw
    #
    wcel
    #
    @20
    com
    cdom
    wbr
    #
    cA
    @20
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @20
    cS
    wcel
    @16
    @28
    @32
    @16
    @14
    cA
    wcel
    @28
    @16
    @14
    cc0
    c2
    cicc
    co
    #
    cA
    @16
    cc0
    c2
    @14
    @16
    0red
    #
    c2
    cr
    wcel
    @16
    2re
    a1i
    #
    @16
    @12
    cr
    @14
    unitssre
    @16
    @14
    cB
    @12
    @16
    id
    salgencntex.b
    syl6eleq
    #
    sseldi
    #
    @16
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    #
    @14
    @12
    wcel
    #
    cc0
    @14
    cle
    wbr
    @16
    cc0
    @34
    rexrd
    #
    @39
    @16
    c1
    1re
    rexri
    a1i
    #
    @36
    cc0
    c1
    @14
    iccgelb
    syl3anc
    @16
    @14
    c1
    c2
    @37
    c1
    cr
    wcel
    @16
    1re
    a1i
    @35
    @16
    @38
    @39
    @40
    @14
    c1
    cle
    wbr
    @41
    @42
    @36
    cc0
    c1
    @14
    iccleub
    syl3anc
    c1
    c2
    cle
    wbr
    @16
    1le2
    a1i
    letrd
    eliccd
    salgencntex.a
    syl6eleqr
    @14
    cA
    snelpwi
    syl
    @16
    @29
    @32
    @29
    @16
    @20
    cfn
    wcel
    @29
    @14
    snfi
    @20
    fict
    ax-mp
    a1i
    @29
    @31
    orc
    syl
    jca
    vx
    cv
    #
    com
    cdom
    wbr
    #
    cA
    @43
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    @32
    vx
    @20
    @27
    cS
    @43
    @20
    wceq
    #
    @44
    @29
    @46
    @31
    @43
    @20
    com
    cdom
    breq1
    @47
    @45
    @30
    com
    cdom
    @43
    @20
    cA
    difeq2
    breq1d
    orbi12d
    salgencntex.s
    elrab2
    sylibr
    @16
    @20
    @11
    cT
    @14
    cB
    snelpwi
    salgencntex.t
    syl6eleqr
    elind
    @13
    cC
    wceq
    @16
    cC
    @13
    salgencntex.c
    eqcomi
    a1i
    eleqtrd
    adantr
    sseldd
    ralrimiva
    vt
    @20
    @6
    @14
    snex
    elint2
    sylibr
    salgencntex.z
    syl6eleqr
    @14
    cB
    snidg
    @18
    @21
    vw
    @20
    cZ
    @17
    @20
    @14
    eleq2
    rspcev
    syl2anc
    vw
    @14
    cZ
    eluni2
    sylibr
    rgen
    vy
    cB
    @1
    dfss3
    mpbir
    eqssi
    cB
    cZ
    wcel
    #
    cB
    cS
    wcel
    #
    cZ
    cS
    cB
    cZ
    @7
    cS
    salgencntex.z
    cS
    @6
    wcel
    #
    @7
    cS
    wss
    @50
    cS
    csalg
    wcel
    #
    cC
    cS
    wss
    #
    wa
    @51
    @52
    @51
    wtru
    vx
    cA
    cS
    cvv
    cA
    cvv
    wcel
    wtru
    cA
    @33
    cvv
    salgencntex.a
    cc0
    c2
    cicc
    ovex
    eqeltri
    a1i
    salgencntex.s
    salexct
    trud
    cC
    @13
    cS
    salgencntex.c
    cS
    cT
    inss1
    eqsstri
    pm3.2i
    @5
    @52
    vs
    cS
    csalg
    @4
    cS
    cC
    sseq2
    elrab
    mpbir
    cS
    @6
    intss1
    ax-mp
    eqsstri
    sseli
    @49
    wn
    @48
    vx
    cA
    cB
    cS
    salgencntex.a
    salgencntex.s
    salgencntex.b
    salexct2
    a1i
    pm2.65i
    eqneltri
    a1i
    pm2.65i
end
