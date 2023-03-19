include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "cres.mm"
include "wf1o.mm"
include "cpw.mm"
include "wrex.mm"
include "cvv.mm"
include "wex.mm"
include "fornex.mm"
include "imp.mm"
include "wceq.mm"
include "foelrn.mm"
include "wi.mm"
include "wfn.mm"
include "fofn.mm"
include "eqcom.mm"
include "fniniseg.mm"
include "biimpar.mm"
include "anassrs.mm"
include "sylan2br.mm"
include "sylanl1.mm"
include "ex.mm"
include "reximdva.mm"
include "adantr.mm"
include "mpd.mm"
include "adantll.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "ac6sg.mm"
include "sylc.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "ad2antrl.mm"
include "vex.mm"
include "rnex.mm"
include "elpw.mm"
include "sylibr.mm"
include "fof.mm"
include "ad2antlr.mm"
include "fssresd.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "fvres.mm"
include "adantl.mm"
include "fveq2d.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "simpr.mm"
include "ad5antlr.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "rspa.mm"
include "syl2anc.mm"
include "simplbda.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "fvelrnb.mm"
include "biimpa.mm"
include "sylan.mm"
include "r19.29af.mm"
include "ffvelrnda.mm"
include "syl.mm"
include "ad3antlr.mm"
include "ralrimi.mm"
include "2fvidf1od.mm"
include "reseq2.mm"
include "id.mm"
include "eqidd.mm"
include "f1oeq123d.mm"
include "rspcev.mm"
include "exlimddv.mm"

theorem foresf1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint A g
  disjoint A y
  disjoint A z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint F g
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ F : A -onto-> B ) -> E. x e. ~P A ( F |` x ) : x -1-1-onto-> B )

  proof
    cA
    cV
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    wa
    #
    cB
    cA
    vg
    cv
    #
    wf
    #
    vy
    cv
    #
    @3
    cfv
    #
    cF
    ccnv
    @5
    csn
    cima
    #
    wcel
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cv
    #
    cB
    cF
    @11
    cres
    #
    wf1o
    #
    vx
    cA
    cpw
    #
    wrex
    #
    vg
    @2
    cB
    cvv
    wcel
    #
    vz
    cv
    #
    @7
    wcel
    #
    vz
    cA
    wrex
    #
    vy
    cB
    wral
    @10
    vg
    wex
    @0
    @1
    @16
    cA
    cB
    cV
    cF
    fornex
    imp
    @2
    @19
    vy
    cB
    @1
    @5
    cB
    wcel
    #
    @19
    @0
    @1
    @20
    wa
    @5
    @17
    cF
    cfv
    #
    wceq
    #
    vz
    cA
    wrex
    #
    @19
    vz
    cA
    cB
    @5
    cF
    foelrn
    @1
    @23
    @19
    wi
    @20
    @1
    @22
    @18
    vz
    cA
    @1
    @17
    cA
    wcel
    #
    wa
    @22
    @18
    @1
    cF
    cA
    wfn
    #
    @24
    @22
    @18
    cA
    cB
    cF
    fofn
    #
    @22
    @25
    @24
    wa
    @21
    @5
    wceq
    #
    @18
    @21
    @5
    eqcom
    @25
    @24
    @27
    @18
    @25
    @18
    @24
    @27
    wa
    cA
    @5
    @17
    cF
    fniniseg
    biimpar
    anassrs
    sylan2br
    sylanl1
    ex
    reximdva
    adantr
    mpd
    adantll
    ralrimiva
    @18
    @8
    vy
    vz
    cB
    cA
    vg
    cvv
    @17
    @6
    @7
    eleq1
    ac6sg
    sylc
    @2
    @10
    wa
    #
    @3
    crn
    #
    @14
    wcel
    #
    @29
    cB
    cF
    @29
    cres
    #
    wf1o
    #
    @15
    @28
    @29
    cA
    wss
    #
    @30
    @4
    @33
    @2
    @9
    cB
    cA
    @3
    frn
    ad2antrl
    #
    @29
    cA
    @3
    vg
    vex
    rnex
    elpw
    sylibr
    @28
    @29
    cB
    @31
    @3
    vz
    vy
    @28
    cA
    cB
    @29
    cF
    @1
    cA
    cB
    cF
    wf
    @0
    @10
    cA
    cB
    cF
    fof
    ad2antlr
    @34
    fssresd
    @28
    @3
    cB
    wfn
    #
    cB
    @29
    @3
    wf
    @4
    @35
    @2
    @9
    cB
    cA
    @3
    ffn
    ad2antrl
    #
    cB
    @3
    dffn3
    sylib
    #
    @28
    @17
    @31
    cfv
    #
    @3
    cfv
    #
    @17
    wceq
    vz
    @29
    @28
    @17
    @29
    wcel
    #
    wa
    #
    @39
    @21
    @3
    cfv
    #
    @17
    @41
    @38
    @21
    @3
    @40
    @38
    @21
    wceq
    @28
    @17
    @29
    cF
    fvres
    adantl
    fveq2d
    @41
    @6
    @17
    wceq
    #
    @42
    @17
    wceq
    vy
    cB
    @28
    @40
    vy
    @2
    @10
    vy
    @2
    vy
    nfv
    @4
    @9
    vy
    @4
    vy
    nfv
    @8
    vy
    cB
    nfra1
    nfan
    nfan
    #
    @40
    vy
    nfv
    nfan
    @41
    @20
    wa
    #
    @43
    wa
    #
    @42
    @6
    @17
    @46
    @21
    @5
    @3
    @46
    @6
    cF
    cfv
    #
    @21
    @5
    @46
    @6
    @17
    cF
    @45
    @43
    simpr
    #
    fveq2d
    @46
    @25
    @8
    @47
    @5
    wceq
    #
    @1
    @25
    @0
    @10
    @40
    @20
    @43
    @26
    ad5antlr
    @46
    @9
    @20
    @8
    @41
    @9
    @20
    @43
    @2
    @4
    @9
    @40
    simplrr
    ad2antrr
    @41
    @20
    @43
    simplr
    @8
    vy
    cB
    rspa
    #
    syl2anc
    @25
    @8
    @6
    cA
    wcel
    @49
    cA
    @5
    @6
    cF
    fniniseg
    simplbda
    #
    syl2anc
    eqtr3d
    fveq2d
    @48
    eqtrd
    @28
    @35
    @40
    @43
    vy
    cB
    wrex
    #
    @36
    @35
    @40
    @52
    vy
    cB
    @17
    @3
    fvelrnb
    biimpa
    sylan
    r19.29af
    eqtrd
    ralrimiva
    @28
    @6
    @31
    cfv
    #
    @5
    wceq
    #
    vy
    cB
    @44
    @28
    @20
    @54
    @28
    @20
    wa
    #
    @53
    @47
    @5
    @55
    @6
    @29
    wcel
    @53
    @47
    wceq
    @28
    cB
    @29
    @5
    @3
    @37
    ffvelrnda
    @6
    @29
    cF
    fvres
    syl
    @55
    @25
    @8
    @49
    @1
    @25
    @0
    @10
    @20
    @26
    ad3antlr
    @55
    @9
    @20
    @8
    @2
    @4
    @9
    @20
    simplrr
    @28
    @20
    simpr
    @50
    syl2anc
    @51
    syl2anc
    eqtrd
    ex
    ralrimi
    2fvidf1od
    @13
    @32
    vx
    @29
    @14
    @11
    @29
    wceq
    #
    @11
    @29
    cB
    cB
    @12
    @31
    @11
    @29
    cF
    reseq2
    @56
    id
    @56
    cB
    eqidd
    f1oeq123d
    rspcev
    syl2anc
    exlimddv
end
