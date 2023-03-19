include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cismty.mm"
include "co.mm"
include "wss.mm"
include "cres.mm"
include "cima.mm"
include "wf1o.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "wf1.mm"
include "isismty.mm"
include "simprbda.mm"
include "adantrr.mm"
include "f1of1.mm"
include "syl.mm"
include "simprr.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "wi.mm"
include "ssel.mm"
include "anim12d.mm"
include "imp.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "an32s.mm"
include "adantlrl.mm"
include "adantlll.mm"
include "cxp.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "adantl.mm"
include "fvres.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "oveq12d.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "f1odm.mm"
include "sseq2d.mm"
include "biimparc.mm"
include "funfvima2.mm"
include "syl6eleqr.mm"
include "adantrl.mm"
include "ovresd.mm"
include "eqtrd.mm"
include "adantlrr.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "mpdan.mm"
include "wb.mm"
include "xmetres2.mm"
include "syl5eqel.mm"
include "ad2ant2rl.mm"
include "simplr.mm"
include "crn.mm"
include "imassrn.mm"
include "eqsstri.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "mpbir2and.mm"

theorem ismtyres
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume ismtyres.2: |- B = ( F " A )
  assume ismtyres.3: |- S = ( M |` ( A X. A ) )
  assume ismtyres.4: |- T = ( N |` ( B X. B ) )


  assert |- ( ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) /\ ( F e. ( M Ismty N ) /\ A C_ X ) ) -> ( F |` A ) e. ( S Ismty T ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    wa
    #
    cF
    cM
    cN
    cismty
    co
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    wa
    #
    cF
    cA
    cres
    #
    cS
    cT
    cismty
    co
    wcel
    #
    cA
    cF
    cA
    cima
    #
    @7
    wf1o
    #
    vu
    cv
    #
    vv
    cv
    #
    cS
    co
    #
    @11
    @7
    cfv
    #
    @12
    @7
    cfv
    #
    cT
    co
    #
    wceq
    #
    vv
    cA
    wral
    vu
    cA
    wral
    #
    @6
    cX
    cY
    cF
    wf1
    #
    @4
    @10
    @6
    cX
    cY
    cF
    wf1o
    #
    @19
    @2
    @3
    @20
    @4
    @2
    @3
    @20
    vx
    cv
    #
    vy
    cv
    #
    cM
    co
    #
    @21
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vx
    vy
    cF
    cM
    cN
    cX
    cY
    isismty
    #
    simprbda
    adantrr
    #
    cX
    cY
    cF
    f1of1
    syl
    @2
    @3
    @4
    simprr
    cX
    cY
    cA
    cF
    f1ores
    syl2anc
    @6
    @20
    @28
    wa
    #
    @18
    @2
    @3
    @31
    @4
    @2
    @3
    @31
    @29
    biimpa
    adantrr
    @2
    @4
    @31
    @18
    @3
    @2
    @4
    wa
    @31
    wa
    #
    @17
    vu
    vv
    cA
    cA
    @32
    @11
    cA
    wcel
    #
    @12
    cA
    wcel
    #
    wa
    #
    wa
    @11
    @12
    cM
    co
    #
    @11
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    cN
    co
    #
    @13
    @16
    @4
    @31
    @35
    @36
    @39
    wceq
    #
    @2
    @4
    @28
    @35
    @40
    @20
    @4
    @35
    @28
    @40
    @4
    @35
    wa
    #
    @28
    @40
    @41
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    wa
    #
    @28
    @40
    wi
    @4
    @35
    @44
    @4
    @33
    @42
    @34
    @43
    cA
    cX
    @11
    ssel
    cA
    cX
    @12
    ssel
    anim12d
    imp
    @27
    @40
    @11
    @22
    cM
    co
    #
    @37
    @25
    cN
    co
    #
    wceq
    vx
    vy
    @11
    @12
    cX
    cX
    @21
    @11
    wceq
    #
    @23
    @45
    @26
    @46
    @21
    @11
    @22
    cM
    oveq1
    @47
    @24
    @37
    @25
    cN
    @21
    @11
    cF
    fveq2
    oveq1d
    eqeq12d
    @22
    @12
    wceq
    #
    @45
    @36
    @46
    @39
    @22
    @12
    @11
    cM
    oveq2
    @48
    @25
    @38
    @37
    cN
    @22
    @12
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl
    imp
    an32s
    adantlrl
    adantlll
    @35
    @13
    @36
    wceq
    @32
    @35
    @13
    @11
    @12
    cM
    cA
    cA
    cxp
    cres
    #
    co
    @36
    cS
    @49
    @11
    @12
    ismtyres.3
    oveqi
    @11
    @12
    cA
    cA
    cM
    ovres
    syl5eq
    adantl
    @4
    @31
    @35
    @16
    @39
    wceq
    #
    @2
    @4
    @20
    @35
    @50
    @28
    @4
    @20
    wa
    #
    @35
    wa
    #
    @16
    @37
    @38
    cT
    co
    #
    @39
    @52
    @14
    @37
    @15
    @38
    cT
    @33
    @14
    @37
    wceq
    @51
    @34
    @11
    cA
    cF
    fvres
    ad2antrl
    @34
    @15
    @38
    wceq
    @51
    @33
    @12
    cA
    cF
    fvres
    ad2antll
    oveq12d
    @52
    @53
    @37
    @38
    cN
    cB
    cB
    cxp
    cres
    #
    co
    @39
    cT
    @54
    @37
    @38
    ismtyres.4
    oveqi
    @52
    @37
    @38
    cN
    cB
    @51
    @33
    @37
    cB
    wcel
    @34
    @51
    @33
    wa
    @37
    @9
    cB
    @51
    @33
    @37
    @9
    wcel
    #
    @51
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    #
    @33
    @55
    wi
    @20
    @56
    @4
    cX
    cY
    cF
    f1ofun
    adantl
    #
    @20
    @58
    @4
    @20
    @57
    cX
    cA
    cX
    cY
    cF
    f1odm
    sseq2d
    biimparc
    #
    cA
    @11
    cF
    funfvima2
    syl2anc
    imp
    ismtyres.2
    syl6eleqr
    adantrr
    @51
    @34
    @38
    cB
    wcel
    @33
    @51
    @34
    wa
    @38
    @9
    cB
    @51
    @34
    @38
    @9
    wcel
    #
    @51
    @56
    @58
    @34
    @61
    wi
    @59
    @60
    cA
    @12
    cF
    funfvima2
    syl2anc
    imp
    ismtyres.2
    syl6eleqr
    adantrl
    ovresd
    syl5eq
    eqtrd
    adantlrr
    adantlll
    3eqtr4d
    ralrimivva
    adantlrl
    mpdan
    @6
    cS
    cA
    cxmt
    cfv
    #
    wcel
    #
    cT
    @9
    cxmt
    cfv
    #
    wcel
    @8
    @10
    @18
    wa
    wb
    @0
    @4
    @63
    @1
    @3
    @0
    @4
    wa
    cS
    @49
    @62
    ismtyres.3
    cM
    cA
    cX
    xmetres2
    syl5eqel
    ad2ant2rl
    @6
    cT
    cB
    cxmt
    cfv
    #
    @64
    @6
    cT
    @54
    @65
    ismtyres.4
    @6
    @1
    cB
    cY
    wss
    @54
    @65
    wcel
    @0
    @1
    @5
    simplr
    @6
    cF
    crn
    #
    cB
    cY
    cB
    @9
    @66
    ismtyres.2
    cF
    cA
    imassrn
    eqsstri
    @6
    @20
    cX
    cY
    cF
    wfo
    @66
    cY
    wceq
    @30
    cX
    cY
    cF
    f1ofo
    cX
    cY
    cF
    forn
    3syl
    syl5sseq
    cN
    cB
    cY
    xmetres2
    syl2anc
    syl5eqel
    cB
    @9
    cxmt
    ismtyres.2
    fveq2i
    syl6eleq
    vu
    vv
    @7
    cS
    cT
    cA
    @9
    isismty
    syl2anc
    mpbir2and
end
