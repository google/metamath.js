include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "c0g.mm"
include "wne.mm"
include "crab.mm"
include "wo.mm"
include "csupp.mm"
include "cun.mm"
include "wn.mm"
include "wceq.mm"
include "ioran.mm"
include "nne.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wfn.mm"
include "elmapfn.mm"
include "ad2antrl.mm"
include "adantr.mm"
include "ad2antll.mm"
include "simplr.mm"
include "inidm.mm"
include "simplrl.mm"
include "simplrr.mm"
include "ofval.mm"
include "an32s.mm"
include "cbs.mm"
include "eqid.mm"
include "mndidcl.mm"
include "ancli.mm"
include "ad4antr.mm"
include "mndlid.mm"
include "syl.mm"
include "eqtrd.mm"
include "sylibr.mm"
include "ex.mm"
include "syl5bi.mm"
include "con4d.mm"
include "ss2rabdv.mm"
include "cdm.mm"
include "wfun.mm"
include "cvv.mm"
include "offn.mm"
include "fnfun.mm"
include "ovex.mm"
include "a1i.mm"
include "fvexd.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "cmpt.mm"
include "offvalfv.mm"
include "dmeqd.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "rabeq.mm"
include "elmapfun.mm"
include "id.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "3syl.mm"
include "simprr.mm"
include "uneq12d.mm"
include "unrab.mm"
include "3sstr4d.mm"

theorem mndpsuppss
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  let vk: setvar k
  assume mndpsuppss.r: |- R = ( Base ` M )


  assert |- ( ( ( M e. Mnd /\ V e. X ) /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) ) -> ( ( A oF ( +g ` M ) B ) supp ( 0g ` M ) ) C_ ( ( A supp ( 0g ` M ) ) u. ( B supp ( 0g ` M ) ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cV
    cX
    wcel
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    #
    wa
    #
    vx
    cv
    #
    cA
    cB
    cM
    cplusg
    cfv
    #
    cof
    #
    co
    #
    cfv
    #
    cM
    c0g
    cfv
    #
    wne
    #
    vx
    cV
    crab
    #
    @8
    cA
    cfv
    #
    @13
    wne
    #
    @8
    cB
    cfv
    #
    @13
    wne
    #
    wo
    #
    vx
    cV
    crab
    #
    @11
    @13
    csupp
    co
    #
    cA
    @13
    csupp
    co
    #
    cB
    @13
    csupp
    co
    #
    cun
    #
    @7
    @14
    @20
    vx
    cV
    @7
    @8
    cV
    wcel
    #
    wa
    #
    @20
    @14
    @20
    wn
    #
    @16
    @13
    wceq
    #
    @18
    @13
    wceq
    #
    wa
    #
    @27
    @14
    wn
    #
    @28
    @17
    wn
    #
    @19
    wn
    #
    wa
    @31
    @17
    @19
    ioran
    @33
    @29
    @34
    @30
    @16
    @13
    nne
    @18
    @13
    nne
    anbi12i
    bitri
    @27
    @31
    @32
    @27
    @31
    wa
    #
    @12
    @13
    wceq
    @32
    @35
    @12
    @13
    @13
    @9
    co
    #
    @13
    @7
    @31
    @26
    @12
    @36
    wceq
    @7
    @31
    wa
    cV
    cV
    @13
    @13
    @9
    cV
    cA
    cB
    cX
    cX
    @8
    @7
    cA
    cV
    wfn
    #
    @31
    @4
    @37
    @2
    @5
    cA
    cR
    cV
    elmapfn
    ad2antrl
    #
    adantr
    @7
    cB
    cV
    wfn
    #
    @31
    @5
    @39
    @2
    @4
    cB
    cR
    cV
    elmapfn
    ad2antll
    #
    adantr
    @7
    @1
    @31
    @0
    @1
    @6
    simplr
    #
    adantr
    #
    @42
    cV
    inidm
    #
    @7
    @29
    @30
    @26
    simplrl
    @7
    @29
    @30
    @26
    simplrr
    ofval
    an32s
    @35
    @0
    @13
    cM
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @36
    @13
    wceq
    @0
    @46
    @1
    @6
    @26
    @31
    @0
    @45
    @44
    cM
    @13
    @44
    eqid
    #
    @13
    eqid
    #
    mndidcl
    ancli
    ad4antr
    @44
    @9
    cM
    @13
    @13
    @47
    @9
    eqid
    @48
    mndlid
    syl
    eqtrd
    @12
    @13
    nne
    sylibr
    ex
    syl5bi
    con4d
    ss2rabdv
    @7
    @22
    @14
    vx
    @11
    cdm
    #
    crab
    #
    @15
    @7
    @11
    wfun
    #
    @11
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    @22
    @50
    wceq
    @7
    @11
    cV
    wfn
    @51
    @7
    cV
    cV
    @9
    cV
    cA
    cB
    cX
    cX
    @38
    @40
    @41
    @41
    @43
    offn
    cV
    @11
    fnfun
    syl
    @52
    @7
    cA
    cB
    @10
    ovex
    a1i
    @7
    cM
    c0g
    fvexd
    #
    vx
    cvv
    cvv
    @11
    @13
    suppval1
    syl3anc
    @7
    @49
    cV
    wceq
    @50
    @15
    wceq
    @7
    @49
    vv
    cV
    vv
    cv
    #
    cA
    cfv
    #
    @55
    cB
    cfv
    #
    @9
    co
    #
    cmpt
    #
    cdm
    cV
    @7
    @11
    @59
    @7
    vv
    cV
    @9
    cA
    cB
    cX
    @41
    @38
    @40
    offvalfv
    dmeqd
    vv
    cV
    @58
    @59
    @56
    @57
    @9
    ovex
    @59
    eqid
    dmmpti
    syl6eq
    @14
    vx
    @49
    cV
    rabeq
    syl
    eqtrd
    @7
    @25
    @17
    vx
    cV
    crab
    #
    @19
    vx
    cV
    crab
    #
    cun
    @21
    @7
    @23
    @60
    @24
    @61
    @4
    @23
    @60
    wceq
    @2
    @5
    @4
    @23
    @17
    vx
    cA
    cdm
    #
    crab
    #
    @60
    @4
    cA
    wfun
    @4
    @53
    @23
    @63
    wceq
    cA
    cR
    cV
    elmapfun
    @4
    id
    @4
    cM
    c0g
    fvexd
    vx
    @3
    cvv
    cA
    @13
    suppval1
    syl3anc
    @4
    cV
    cR
    cA
    wf
    @62
    cV
    wceq
    @63
    @60
    wceq
    cA
    cR
    cV
    elmapi
    cV
    cR
    cA
    fdm
    @17
    vx
    @62
    cV
    rabeq
    3syl
    eqtrd
    ad2antrl
    @7
    @24
    @19
    vx
    cB
    cdm
    #
    crab
    #
    @61
    @7
    cB
    wfun
    #
    @5
    @53
    @24
    @65
    wceq
    @5
    @66
    @2
    @4
    cB
    cR
    cV
    elmapfun
    ad2antll
    @2
    @4
    @5
    simprr
    @54
    vx
    @3
    cvv
    cB
    @13
    suppval1
    syl3anc
    @7
    @64
    cV
    wceq
    #
    @65
    @61
    wceq
    @5
    @67
    @2
    @4
    @5
    cV
    cR
    cB
    wf
    @67
    cB
    cR
    cV
    elmapi
    cV
    cR
    cB
    fdm
    syl
    ad2antll
    @19
    vx
    @64
    cV
    rabeq
    syl
    eqtrd
    uneq12d
    @17
    @19
    vx
    cV
    unrab
    syl6eq
    3sstr4d
end
