include "cfn.mm"
include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cima.mm"
include "cdom.mm"
include "wceq.mm"
include "foima.mm"
include "adantl.mm"
include "wbr.mm"
include "wfn.mm"
include "fofn.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "imaeq2.mm"
include "ima0.mm"
include "syl6eq.mm"
include "id.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "0ex.mm"
include "0dom.mm"
include "a1i.mm"
include "wn.mm"
include "cid.mm"
include "cfv.mm"
include "cvv.mm"
include "wss.mm"
include "cres.mm"
include "crn.mm"
include "cop.mm"
include "wfun.mm"
include "fnfun.mm"
include "ad2antrl.mm"
include "funressn.mm"
include "rnss.mm"
include "3syl.mm"
include "df-ima.mm"
include "vex.mm"
include "rnsnop.mm"
include "eqcomi.mm"
include "3sstr4g.mm"
include "snex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "fvi.mm"
include "syl.mm"
include "uneq2d.mm"
include "imaundi.mm"
include "syl6eqr.mm"
include "cin.mm"
include "simprr.mm"
include "cen.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "c1o.mm"
include "fvex.mm"
include "ensn1.mm"
include "entr4i.mm"
include "domentr.mm"
include "eqbrtrd.mm"
include "simplr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "undom.mm"
include "syl21anc.mm"
include "eqbrtrrd.mm"
include "exp32.mm"
include "a2d.mm"
include "findcard2s.mm"
include "syl5.mm"
include "imp.mm"

theorem fodomfi
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. Fin /\ F : A -onto-> B ) -> B ~<_ A )

  proof
    cA
    cfn
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    wa
    cF
    cA
    cima
    #
    cB
    cA
    cdom
    @1
    @2
    cB
    wceq
    @0
    cA
    cB
    cF
    foima
    adantl
    @0
    @1
    @2
    cA
    cdom
    wbr
    #
    @1
    cF
    cA
    wfn
    #
    @0
    @3
    cA
    cB
    cF
    fofn
    @4
    cF
    vx
    cv
    #
    cima
    #
    @5
    cdom
    wbr
    #
    wi
    @4
    c0
    c0
    cdom
    wbr
    #
    wi
    @4
    cF
    vy
    cv
    #
    cima
    #
    @9
    cdom
    wbr
    #
    wi
    @4
    cF
    @9
    vz
    cv
    #
    csn
    #
    cun
    #
    cima
    #
    @14
    cdom
    wbr
    #
    wi
    @4
    @3
    wi
    vx
    vy
    vz
    cA
    @5
    c0
    wceq
    #
    @7
    @8
    @4
    @17
    @6
    c0
    @5
    c0
    cdom
    @17
    @6
    cF
    c0
    cima
    c0
    @5
    c0
    cF
    imaeq2
    cF
    ima0
    syl6eq
    @17
    id
    breq12d
    imbi2d
    @5
    @9
    wceq
    #
    @7
    @11
    @4
    @18
    @6
    @10
    @5
    @9
    cdom
    @5
    @9
    cF
    imaeq2
    @18
    id
    breq12d
    imbi2d
    @5
    @14
    wceq
    #
    @7
    @16
    @4
    @19
    @6
    @15
    @5
    @14
    cdom
    @5
    @14
    cF
    imaeq2
    @19
    id
    breq12d
    imbi2d
    @5
    cA
    wceq
    #
    @7
    @3
    @4
    @20
    @6
    @2
    @5
    cA
    cdom
    @5
    cA
    cF
    imaeq2
    @20
    id
    breq12d
    imbi2d
    @8
    @4
    c0
    0ex
    0dom
    a1i
    @9
    cfn
    wcel
    #
    @12
    @9
    wcel
    wn
    #
    wa
    #
    @4
    @11
    @16
    @23
    @4
    @11
    @16
    @23
    @4
    @11
    wa
    #
    wa
    #
    @10
    cF
    @13
    cima
    #
    cid
    cfv
    #
    cun
    #
    @15
    @14
    cdom
    @25
    @28
    @10
    @26
    cun
    @15
    @25
    @27
    @26
    @10
    @25
    @26
    cvv
    wcel
    #
    @27
    @26
    wceq
    @25
    @26
    @12
    cF
    cfv
    #
    csn
    #
    wss
    #
    @31
    cvv
    wcel
    #
    @29
    @25
    cF
    @13
    cres
    #
    crn
    #
    @12
    @30
    cop
    csn
    #
    crn
    #
    @26
    @31
    @25
    cF
    wfun
    #
    @34
    @36
    wss
    @35
    @37
    wss
    @4
    @38
    @23
    @11
    cA
    cF
    fnfun
    ad2antrl
    @12
    cF
    funressn
    @34
    @36
    rnss
    3syl
    cF
    @13
    df-ima
    @37
    @31
    @12
    @30
    vz
    vex
    #
    rnsnop
    eqcomi
    3sstr4g
    #
    @30
    snex
    #
    @26
    @31
    cvv
    ssexg
    sylancl
    @26
    cvv
    fvi
    syl
    #
    uneq2d
    cF
    @9
    @13
    imaundi
    syl6eqr
    @25
    @11
    @27
    @13
    cdom
    wbr
    @9
    @13
    cin
    c0
    wceq
    #
    @28
    @14
    cdom
    wbr
    @23
    @4
    @11
    simprr
    @25
    @27
    @26
    @13
    cdom
    @42
    @25
    @26
    @31
    cdom
    wbr
    #
    @31
    @13
    cen
    wbr
    @26
    @13
    cdom
    wbr
    @33
    @25
    @32
    @44
    @41
    @40
    @26
    @31
    cvv
    ssdomg
    mpsyl
    @31
    c1o
    @13
    @30
    @12
    cF
    fvex
    ensn1
    @12
    @39
    ensn1
    entr4i
    @26
    @31
    @13
    domentr
    sylancl
    eqbrtrd
    @25
    @22
    @43
    @21
    @22
    @24
    simplr
    @9
    @12
    disjsn
    sylibr
    @10
    @9
    @27
    @13
    undom
    syl21anc
    eqbrtrrd
    exp32
    a2d
    findcard2s
    syl5
    imp
    eqbrtrrd
end
