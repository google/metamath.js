include "csalgen.mm"
include "cfv.mm"
include "wceq.mm"
include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "salgencl.mm"
include "syl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "unieq.mm"
include "eqid.mm"
include "salgenuni.mm"
include "eqtr3d.mm"
include "sssalgen.mm"
include "simpr.mm"
include "sseqtrd.mm"
include "3jca.mm"
include "ad2antrr.mm"
include "adantrl.mm"
include "simplr.mm"
include "simprl.mm"
include "salgenss.mm"
include "eqsstrd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "jca.mm"
include "simprl1.mm"
include "simprl2.mm"
include "simprl3.mm"
include "eqeq1d.mm"
include "sseq2.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "3ad2antr1.mm"
include "3simpc.mm"
include "rspa.mm"
include "sylc.mm"
include "adantll.mm"
include "issalgend.mm"
include "impbid.mm"

theorem dfsalgen2
  let wph: wff ph
  let vy: setvar y
  let cS: class S
  let cV: class V
  let cX: class X
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x
  assume dfsalgen2.1: |- ( ph -> X e. V )

  disjoint S y
  disjoint X y
  disjoint ph y
  disjoint S w
  disjoint w y
  disjoint X w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> ( ( SalGen ` X ) = S <-> ( ( S e. SAlg /\ U. S = U. X /\ X C_ S ) /\ A. y e. SAlg ( ( U. y = U. X /\ X C_ y ) -> S C_ y ) ) ) )

  proof
    wph
    cX
    csalgen
    cfv
    #
    cS
    wceq
    #
    cS
    csalg
    wcel
    #
    cS
    cuni
    #
    cX
    cuni
    #
    wceq
    #
    cX
    cS
    wss
    #
    w3a
    #
    vy
    cv
    #
    cuni
    #
    @4
    wceq
    #
    cX
    @8
    wss
    #
    wa
    #
    cS
    @8
    wss
    #
    wi
    #
    vy
    csalg
    wral
    #
    wa
    #
    wph
    @1
    @16
    wph
    @1
    wa
    #
    @7
    @15
    @17
    @2
    @5
    @6
    @17
    cS
    @0
    csalg
    @1
    cS
    @0
    wceq
    #
    wph
    @1
    @0
    cS
    @1
    id
    eqcomd
    adantl
    #
    wph
    @0
    csalg
    wcel
    #
    @1
    wph
    cX
    cV
    wcel
    #
    @20
    dfsalgen2.1
    cV
    cX
    salgencl
    syl
    adantr
    eqeltrd
    @17
    @0
    cuni
    #
    @3
    @4
    @1
    @22
    @3
    wceq
    wph
    @0
    cS
    unieq
    adantl
    @17
    @0
    @4
    cV
    cX
    wph
    @21
    @1
    dfsalgen2.1
    adantr
    #
    @0
    eqid
    #
    @4
    eqid
    salgenuni
    eqtr3d
    @17
    cX
    @0
    cS
    @17
    @21
    cX
    @0
    wss
    @23
    @0
    cV
    cX
    @24
    sssalgen
    syl
    wph
    @1
    simpr
    sseqtrd
    3jca
    @17
    @14
    vy
    csalg
    @17
    @8
    csalg
    wcel
    #
    wa
    #
    @12
    @13
    @26
    @12
    wa
    #
    cS
    @0
    @8
    @26
    @11
    @18
    @10
    @17
    @18
    @25
    @11
    @19
    ad2antrr
    adantrl
    @27
    @8
    @0
    cV
    cX
    @26
    @11
    @21
    @10
    @17
    @21
    @25
    @11
    @23
    ad2antrr
    adantrl
    @24
    @26
    @11
    @25
    @10
    @17
    @25
    @11
    simplr
    adantrl
    @26
    @11
    @11
    @10
    @26
    @11
    simpr
    adantrl
    @26
    @10
    @11
    simprl
    salgenss
    eqsstrd
    ex
    ralrimiva
    jca
    ex
    wph
    @16
    @1
    wph
    @16
    wa
    vw
    cS
    cV
    cX
    wph
    @21
    @16
    dfsalgen2.1
    adantr
    @2
    @5
    @6
    @15
    wph
    simprl1
    @2
    @5
    @6
    @15
    wph
    simprl2
    @2
    @5
    @6
    @15
    wph
    simprl3
    @16
    vw
    cv
    #
    csalg
    wcel
    #
    @28
    cuni
    #
    @4
    wceq
    #
    cX
    @28
    wss
    #
    w3a
    #
    cS
    @28
    wss
    #
    wph
    @15
    @33
    @34
    @7
    @15
    @33
    wa
    @31
    @32
    wa
    #
    @34
    wi
    #
    vw
    csalg
    wral
    #
    @29
    wa
    #
    @35
    @34
    @15
    @31
    @29
    @38
    @32
    @15
    @29
    wa
    @37
    @29
    @15
    @37
    @29
    @15
    @37
    @14
    @36
    vy
    vw
    csalg
    @8
    @28
    wceq
    #
    @12
    @35
    @13
    @34
    @39
    @10
    @31
    @11
    @32
    @39
    @9
    @30
    @4
    @8
    @28
    unieq
    eqeq1d
    @8
    @28
    cX
    sseq2
    anbi12d
    @8
    @28
    cS
    sseq2
    imbi12d
    cbvralv
    biimpi
    adantr
    @15
    @29
    simpr
    jca
    3ad2antr1
    @33
    @35
    @15
    @29
    @31
    @32
    3simpc
    adantl
    @36
    vw
    csalg
    rspa
    sylc
    adantll
    adantll
    issalgend
    ex
    impbid
end
