include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "c0g.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "cdiv.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "rspcv.mm"
include "ad3antlr.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "cngp.mm"
include "cbs.mm"
include "cghm.mm"
include "isnghm.mm"
include "simplbi.mm"
include "adantr.mm"
include "simprd.mm"
include "wf.mm"
include "simprbi.mm"
include "simpld.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "elrege0.mm"
include "adantl.mm"
include "crp.mm"
include "simpr.mm"
include "jca.mm"
include "nmrpcl.mm"
include "3expa.mm"
include "sylan.mm"
include "rpregt0d.mm"
include "ledivmul2.mm"
include "syl3anc.mm"
include "sylibrd.mm"
include "ralrimiva.mm"
include "cxr.mm"
include "rerpdivcld.mm"
include "rexrd.mm"
include "nmogelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "ledivmul2d.mm"
include "mpbid.mm"
include "ghmid.mm"
include "nm0.mm"
include "eqtrd.mm"
include "0re.mm"
include "syl6eqel.mm"
include "nmoge0.mm"
include "0le0.mm"
include "syl5breqr.mm"
include "mulge0d.mm"
include "eqbrtrd.mm"
include "pm2.61ne.mm"

theorem nmoi
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cA: class A
  let wph: wff ph
  assume nmofval.1: |- N = ( S normOp T )
  assume nmoi.2: |- V = ( Base ` S )
  assume nmoi.3: |- L = ( norm ` S )
  assume nmoi.4: |- M = ( norm ` T )


  assert |- ( ( F e. ( S NGHom T ) /\ X e. V ) -> ( M ` ( F ` X ) ) <_ ( ( N ` F ) x. ( L ` X ) ) )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    cF
    cfv
    #
    cM
    cfv
    #
    cF
    cN
    cfv
    #
    cX
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cS
    c0g
    cfv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    @5
    @9
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    cX
    @9
    cX
    @9
    wceq
    #
    @4
    @11
    @7
    @13
    cle
    @14
    @3
    @10
    cM
    cX
    @9
    cF
    fveq2
    fveq2d
    @14
    @6
    @12
    @5
    cmul
    cX
    @9
    cL
    fveq2
    oveq2d
    breq12d
    @2
    cX
    @9
    wne
    #
    wa
    #
    @4
    @6
    cdiv
    co
    #
    @5
    cle
    wbr
    #
    @8
    @16
    @18
    vx
    cv
    #
    cF
    cfv
    #
    cM
    cfv
    #
    vr
    cv
    #
    @19
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    cV
    wral
    #
    @17
    @22
    cle
    wbr
    #
    wi
    #
    vr
    cc0
    cpnf
    cico
    co
    #
    wral
    #
    @16
    @28
    vr
    @29
    @16
    @22
    @29
    wcel
    #
    wa
    #
    @26
    @4
    @22
    @6
    cmul
    co
    #
    cle
    wbr
    #
    @27
    @1
    @26
    @34
    wi
    @0
    @15
    @31
    @25
    @34
    vx
    cX
    cV
    @19
    cX
    wceq
    #
    @21
    @4
    @24
    @33
    cle
    @35
    @20
    @3
    cM
    @19
    cX
    cF
    fveq2
    fveq2d
    @35
    @23
    @6
    @22
    cmul
    @19
    cX
    cL
    fveq2
    oveq2d
    breq12d
    rspcv
    ad3antlr
    @32
    @4
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @6
    cr
    wcel
    cc0
    @6
    clt
    wbr
    wa
    #
    @27
    @34
    wb
    @16
    @36
    @31
    @2
    @36
    @15
    @2
    cT
    cngp
    wcel
    #
    @3
    cT
    cbs
    cfv
    #
    wcel
    #
    @36
    @2
    cS
    cngp
    wcel
    #
    @39
    @0
    @42
    @39
    wa
    #
    @1
    @0
    @43
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @5
    cr
    wcel
    #
    wa
    #
    cS
    cT
    cF
    cN
    nmofval.1
    isnghm
    #
    simplbi
    adantr
    #
    simprd
    #
    @0
    @1
    cV
    @40
    cF
    wf
    #
    @41
    @2
    @44
    @50
    @2
    @44
    @45
    @0
    @46
    @1
    @0
    @43
    @46
    @47
    simprbi
    adantr
    #
    simpld
    #
    cS
    cT
    cF
    cV
    @40
    nmoi.2
    @40
    eqid
    #
    ghmf
    syl
    cV
    @40
    cX
    cF
    ffvelrn
    sylancom
    @3
    cT
    cM
    @40
    @53
    nmoi.4
    nmcl
    syl2anc
    adantr
    #
    adantr
    @31
    @37
    @16
    @31
    @37
    cc0
    @22
    cle
    wbr
    @22
    elrege0
    simplbi
    adantl
    @16
    @38
    @31
    @16
    @6
    @2
    @42
    @1
    wa
    @15
    @6
    crp
    wcel
    #
    @2
    @42
    @1
    @2
    @42
    @39
    @48
    simpld
    #
    @0
    @1
    simpr
    jca
    @42
    @1
    @15
    @55
    cX
    cS
    cL
    cV
    @9
    nmoi.2
    nmoi.3
    @9
    eqid
    #
    nmrpcl
    3expa
    sylan
    #
    rpregt0d
    adantr
    @4
    @22
    @6
    ledivmul2
    syl3anc
    sylibrd
    ralrimiva
    @16
    @42
    @39
    @44
    @17
    cxr
    wcel
    @18
    @30
    wb
    @2
    @42
    @15
    @56
    adantr
    @2
    @39
    @15
    @49
    adantr
    @2
    @44
    @15
    @52
    adantr
    @16
    @17
    @16
    @4
    @6
    @54
    @58
    rerpdivcld
    rexrd
    vx
    @17
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    vr
    nmofval.1
    nmoi.2
    nmoi.3
    nmoi.4
    nmogelb
    syl31anc
    mpbird
    @16
    @4
    @5
    @6
    @54
    @2
    @45
    @15
    @2
    @44
    @45
    @51
    simprd
    #
    adantr
    @58
    ledivmul2d
    mpbid
    @2
    @11
    cc0
    @13
    cle
    @2
    @11
    cT
    c0g
    cfv
    #
    cM
    cfv
    #
    cc0
    @2
    @10
    @60
    cM
    @2
    @44
    @10
    @60
    wceq
    @52
    cS
    cT
    cF
    @9
    @60
    @57
    @60
    eqid
    #
    ghmid
    syl
    fveq2d
    @2
    @39
    @61
    cc0
    wceq
    @49
    cT
    cM
    @60
    nmoi.4
    @62
    nm0
    syl
    eqtrd
    @2
    @5
    @12
    @59
    @2
    @12
    cc0
    cr
    @2
    @42
    @12
    cc0
    wceq
    @56
    cS
    cL
    @9
    nmoi.3
    @57
    nm0
    syl
    #
    0re
    syl6eqel
    @2
    @42
    @39
    @44
    cc0
    @5
    cle
    wbr
    @56
    @49
    @52
    cS
    cT
    cF
    cN
    nmofval.1
    nmoge0
    syl3anc
    @2
    cc0
    cc0
    @12
    cle
    0le0
    @63
    syl5breqr
    mulge0d
    eqbrtrd
    pm2.61ne
end
