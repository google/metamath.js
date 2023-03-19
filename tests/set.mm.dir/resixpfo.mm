include "wss.mm"
include "cixp.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "cres.mm"
include "resixp.mm"
include "fmptd.mm"
include "adantr.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "cif.mm"
include "cmpt.mm"
include "eleq1.mm"
include "ifbid.mm"
include "id.mm"
include "fveq12d.mm"
include "cbvmptv.mm"
include "wfn.mm"
include "vex.mm"
include "elixp.mm"
include "simprbi.mm"
include "wi.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "simpl.mm"
include "imp.mm"
include "wn.mm"
include "simplrr.mm"
include "ifbothda.mm"
include "exp32.mm"
include "ralimi2.mm"
include "syl.mm"
include "adantl.mm"
include "ralim.mm"
include "sylan2.mm"
include "cvv.mm"
include "wb.mm"
include "n0i.mm"
include "ixpprc.mm"
include "nsyl2.mm"
include "mptelixpg.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "iftrue.mm"
include "fveq1d.mm"
include "mpteq2ia.mm"
include "resmpt.mm"
include "ad2antrr.mm"
include "ixpfn.mm"
include "ad2antlr.mm"
include "dffn5.mm"
include "sylib.mm"
include "3eqtr4a.mm"
include "syl6eqel.mm"
include "reseq1.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "ralrimdva.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem resixpfo
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  assume resixpfo.1: |- F = ( f e. X_ x e. A C |-> ( f |` B ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint C f
  disjoint f g
  disjoint f h
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B g
  disjoint B h
  disjoint B y
  disjoint B z
  disjoint C g
  disjoint C h
  disjoint C y
  disjoint F g
  disjoint F h
  disjoint F y
  assert |- ( ( B C_ A /\ X_ x e. A C =/= (/) ) -> F : X_ x e. A C -onto-> X_ x e. B C )

  proof
    cB
    cA
    wss
    #
    vx
    cA
    cC
    cixp
    #
    c0
    wne
    #
    wa
    @1
    vx
    cB
    cC
    cixp
    #
    cF
    wf
    #
    vh
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @1
    wrex
    #
    vh
    @3
    wral
    #
    @1
    @3
    cF
    wfo
    @0
    @4
    @2
    @0
    vf
    @1
    vf
    cv
    #
    cB
    cres
    #
    @3
    cF
    vx
    cA
    cB
    cC
    @11
    resixp
    resixpfo.1
    fmptd
    adantr
    @0
    @2
    @10
    @2
    vg
    cv
    #
    @1
    wcel
    #
    vg
    wex
    @0
    @10
    vg
    @1
    n0
    @0
    @14
    @10
    vg
    @0
    @14
    @9
    vh
    @3
    @0
    @5
    @3
    wcel
    #
    wa
    #
    @14
    @9
    @16
    @14
    wa
    #
    vz
    cA
    vz
    cv
    #
    @18
    cB
    wcel
    #
    @5
    @13
    cif
    #
    cfv
    #
    cmpt
    #
    @1
    wcel
    #
    @5
    @22
    cF
    cfv
    #
    wceq
    #
    @9
    @17
    @22
    vx
    cA
    vx
    cv
    #
    @26
    cB
    wcel
    #
    @5
    @13
    cif
    #
    cfv
    #
    cmpt
    #
    @1
    vz
    vx
    cA
    @21
    @29
    @18
    @26
    wceq
    #
    @18
    @26
    @20
    @28
    @31
    @19
    @27
    @5
    @13
    @18
    @26
    cB
    eleq1
    ifbid
    @31
    id
    fveq12d
    cbvmptv
    @17
    @30
    @1
    wcel
    #
    @29
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @14
    @16
    @26
    @13
    cfv
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @34
    @14
    @13
    cA
    wfn
    @37
    vx
    cA
    cC
    @13
    vg
    vex
    elixp
    simprbi
    @16
    @37
    @34
    @16
    @36
    @33
    wi
    #
    vx
    cA
    wral
    #
    @37
    @34
    wi
    @15
    @39
    @0
    @15
    @26
    @5
    cfv
    #
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @39
    @15
    @5
    cB
    wfn
    #
    @42
    vx
    cB
    cC
    @5
    vh
    vex
    #
    elixp
    simprbi
    @41
    @38
    vx
    cB
    cA
    @27
    @41
    wi
    #
    @26
    cA
    wcel
    #
    @36
    @33
    @27
    @41
    @36
    @33
    @45
    @46
    @36
    wa
    #
    wa
    #
    @5
    @13
    @5
    @28
    wceq
    @40
    @29
    cC
    @26
    @5
    @28
    fveq1
    eleq1d
    @13
    @28
    wceq
    @35
    @29
    cC
    @26
    @13
    @28
    fveq1
    eleq1d
    @48
    @27
    @41
    @45
    @47
    simpl
    imp
    @45
    @46
    @36
    @27
    wn
    simplrr
    ifbothda
    exp32
    ralimi2
    syl
    adantl
    @36
    @33
    vx
    cA
    ralim
    syl
    imp
    sylan2
    @17
    cA
    cvv
    wcel
    #
    @32
    @34
    wb
    @14
    @49
    @16
    @14
    @1
    c0
    wceq
    @49
    @1
    @13
    n0i
    vx
    cA
    cC
    ixpprc
    nsyl2
    adantl
    vx
    cA
    @29
    cC
    cvv
    mptelixpg
    syl
    mpbird
    syl5eqel
    #
    @17
    @24
    @22
    cB
    cres
    #
    @5
    @17
    @23
    @51
    cvv
    wcel
    @24
    @51
    wceq
    @50
    @17
    @51
    @5
    cvv
    @17
    vz
    cB
    @21
    cmpt
    #
    vz
    cB
    @18
    @5
    cfv
    #
    cmpt
    #
    @51
    @5
    vz
    cB
    @21
    @53
    @19
    @18
    @20
    @5
    @19
    @5
    @13
    iftrue
    fveq1d
    mpteq2ia
    @0
    @51
    @52
    wceq
    @15
    @14
    vz
    cA
    cB
    @21
    resmpt
    ad2antrr
    @17
    @43
    @5
    @54
    wceq
    @15
    @43
    @0
    @14
    vx
    cB
    cC
    @5
    ixpfn
    ad2antlr
    vz
    cB
    @5
    dffn5
    sylib
    3eqtr4a
    #
    @44
    syl6eqel
    vf
    @22
    @12
    @51
    @1
    cvv
    cF
    @11
    @22
    cB
    reseq1
    resixpfo.1
    fvmptg
    syl2anc
    @55
    eqtr2d
    @8
    @25
    vy
    @22
    @1
    @6
    @22
    wceq
    @7
    @24
    @5
    @6
    @22
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    ex
    ralrimdva
    exlimdv
    syl5bi
    imp
    vy
    vh
    @1
    @3
    cF
    dffo3
    sylanbrc
end
