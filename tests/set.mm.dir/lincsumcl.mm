include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "cv.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "eqid.mm"
include "lcoval.mm"
include "anbi12d.mm"
include "simpll.mm"
include "adantl.mm"
include "simprl.mm"
include "lmodvacl.mm"
include "syl3anc.mm"
include "wi.mm"
include "cplusg.mm"
include "cof.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "simpl.mm"
include "anim12i.mm"
include "ofaddmndmap.mm"
include "anim1i.mm"
include "mndpfsupp.mm"
include "oveq12.mm"
include "expcom.mm"
include "com12.mm"
include "imp.mm"
include "lincsum.mm"
include "eqtrd.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exp41.mm"
include "rexlimiva.mm"
include "expd.mm"
include "impcom.mm"
include "com13.mm"
include "wb.mm"
include "mpbir2and.mm"
include "ex.mm"
include "sylbid.mm"

theorem lincsumcl
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lincsumcl.b: |- .+ = ( +g ` M )


  assert |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\ ( C e. ( M LinCo V ) /\ D e. ( M LinCo V ) ) ) -> ( C .+ D ) e. ( M LinCo V ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    wa
    #
    cC
    cM
    cV
    clinco
    co
    #
    wcel
    #
    cD
    @5
    wcel
    #
    wa
    #
    cC
    cD
    c.pl
    co
    #
    @5
    wcel
    #
    @4
    @8
    cC
    @1
    wcel
    #
    vy
    cv
    #
    cM
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    cC
    @12
    cV
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vy
    @13
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wrex
    #
    wa
    #
    cD
    @1
    wcel
    #
    vx
    cv
    #
    @14
    cfsupp
    wbr
    #
    cD
    @25
    cV
    @16
    co
    #
    wceq
    #
    wa
    #
    vx
    @21
    wrex
    #
    wa
    #
    wa
    #
    @10
    @4
    @6
    @23
    @7
    @31
    @1
    cC
    @20
    @13
    cM
    cV
    clmod
    vy
    @1
    eqid
    #
    @13
    eqid
    #
    @20
    eqid
    #
    lcoval
    @1
    cD
    @20
    @13
    cM
    cV
    clmod
    vx
    @33
    @34
    @35
    lcoval
    anbi12d
    @4
    @32
    @10
    @4
    @32
    wa
    #
    @10
    @9
    @1
    wcel
    #
    vs
    cv
    #
    @14
    cfsupp
    wbr
    #
    @9
    @38
    cV
    @16
    co
    #
    wceq
    #
    wa
    #
    vs
    @21
    wrex
    #
    @36
    @0
    @11
    @24
    @37
    @0
    @3
    @32
    simpll
    @32
    @11
    @4
    @11
    @22
    @31
    simpll
    adantl
    @32
    @24
    @4
    @23
    @24
    @30
    simprl
    adantl
    c.pl
    @1
    cM
    cC
    cD
    @33
    lincsumcl.b
    lmodvacl
    syl3anc
    @32
    @4
    @43
    @31
    @23
    @4
    @43
    wi
    #
    @30
    @24
    @23
    @44
    wi
    #
    @29
    @24
    @45
    wi
    vx
    @21
    @23
    @24
    @25
    @21
    wcel
    #
    @29
    wa
    #
    @44
    @22
    @11
    @24
    @47
    @44
    wi
    #
    wi
    @22
    @11
    @24
    @48
    @19
    @11
    @24
    wa
    #
    @48
    wi
    vy
    @21
    @12
    @21
    wcel
    #
    @19
    wa
    #
    @49
    @47
    @4
    @43
    @51
    @49
    wa
    #
    @47
    wa
    #
    @4
    wa
    #
    @12
    @25
    @13
    cplusg
    cfv
    #
    cof
    co
    #
    @21
    wcel
    #
    @56
    @14
    cfsupp
    wbr
    #
    @9
    @56
    cV
    @16
    co
    #
    wceq
    #
    @43
    @54
    @13
    cmnd
    wcel
    #
    @3
    @50
    @46
    wa
    #
    @57
    @4
    @61
    @53
    @0
    @61
    @3
    @0
    @13
    cgrp
    wcel
    @61
    @13
    cM
    @34
    lmodfgrp
    @13
    grpmnd
    syl
    #
    adantr
    adantl
    @4
    @3
    @53
    @0
    @3
    simpr
    adantl
    @53
    @62
    @4
    @52
    @50
    @47
    @46
    @50
    @19
    @49
    simpll
    @46
    @29
    simpl
    anim12i
    adantr
    #
    @12
    @25
    @55
    @20
    @13
    cV
    @2
    @35
    @55
    eqid
    #
    ofaddmndmap
    syl3anc
    @54
    @61
    @3
    wa
    #
    @62
    @15
    @26
    wa
    #
    @58
    @4
    @66
    @53
    @0
    @61
    @3
    @63
    anim1i
    adantl
    @64
    @53
    @67
    @4
    @52
    @15
    @47
    @26
    @51
    @15
    @49
    @50
    @15
    @18
    simprl
    adantr
    @46
    @26
    @28
    simprl
    anim12i
    adantr
    #
    @12
    @25
    @20
    @13
    cV
    @2
    @35
    mndpfsupp
    syl3anc
    @54
    @9
    @17
    @27
    c.pl
    co
    #
    @59
    @53
    @9
    @69
    wceq
    #
    @4
    @52
    @47
    @70
    @51
    @47
    @70
    wi
    #
    @49
    @19
    @71
    @50
    @18
    @71
    @15
    @47
    @18
    @70
    @29
    @18
    @70
    wi
    #
    @46
    @28
    @72
    @26
    @18
    @28
    @70
    cC
    @17
    cD
    @27
    c.pl
    oveq12
    expcom
    adantl
    adantl
    com12
    adantl
    adantl
    adantr
    imp
    adantr
    @54
    @4
    @62
    @67
    @69
    @59
    wceq
    @53
    @4
    simpr
    @64
    @68
    @12
    @25
    c.pl
    @55
    @20
    @13
    cM
    cV
    @17
    @27
    lincsumcl.b
    @17
    eqid
    @27
    eqid
    @34
    @35
    @65
    lincsum
    syl3anc
    eqtrd
    @42
    @58
    @60
    wa
    vs
    @56
    @21
    @38
    @56
    wceq
    #
    @39
    @58
    @41
    @60
    @38
    @56
    @14
    cfsupp
    breq1
    @73
    @40
    @59
    @9
    @38
    @56
    cV
    @16
    oveq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    exp41
    rexlimiva
    expd
    impcom
    com13
    rexlimiva
    impcom
    impcom
    impcom
    @4
    @10
    @37
    @43
    wa
    wb
    @32
    @1
    @9
    @20
    @13
    cM
    cV
    clmod
    vs
    @33
    @34
    @35
    lcoval
    adantr
    mpbir2and
    ex
    sylbid
    imp
end
