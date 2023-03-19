include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cur.mm"
include "cvsca.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "eqid.mm"
include "scmatel.mm"
include "oveq12.mm"
include "adantll.mm"
include "simp-4l.mm"
include "simplr.mm"
include "anim1i.mm"
include "ancomd.mm"
include "scmatscmiddistr.mm"
include "syl2anc.mm"
include "simpl.mm"
include "simprr.mm"
include "adantl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "matring.mm"
include "ringidcl.mm"
include "syl.mm"
include "adantr.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "mpbir2and.mm"
include "exp32.mm"
include "imp.mm"
include "eqeltrd.mm"
include "exp31.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "com23.mm"
include "sylbid.mm"
include "imp32.mm"

theorem scmatmulcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vd: setvar d
  let ve: setvar e
  let vc: setvar c
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( X e. S /\ Y e. S ) ) -> ( X ( .r ` A ) Y ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    cX
    cY
    cA
    cmulr
    cfv
    #
    co
    #
    cS
    wcel
    #
    @2
    @3
    cX
    cB
    wcel
    #
    cX
    vc
    cv
    #
    cA
    cur
    cfv
    #
    cA
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cE
    wrex
    #
    wa
    #
    @4
    @7
    wi
    cA
    cB
    cR
    cS
    @11
    @10
    cE
    cX
    cN
    crg
    vc
    scmatid.e
    scmatid.a
    scmatid.b
    @10
    eqid
    #
    @11
    eqid
    #
    scmatid.s
    scmatel
    @2
    @4
    @15
    @7
    @2
    @4
    cY
    cB
    wcel
    #
    cY
    vd
    cv
    #
    @10
    @11
    co
    #
    wceq
    #
    vd
    cE
    wrex
    #
    wa
    @15
    @7
    wi
    #
    cA
    cB
    cR
    cS
    @11
    @10
    cE
    cY
    cN
    crg
    vd
    scmatid.e
    scmatid.a
    scmatid.b
    @16
    @17
    scmatid.s
    scmatel
    @2
    @18
    @22
    @23
    @2
    @18
    wa
    #
    @21
    @23
    vd
    cE
    @24
    @19
    cE
    wcel
    #
    wa
    #
    @15
    @21
    @7
    @26
    @8
    @14
    @21
    @7
    wi
    #
    @26
    @8
    wa
    #
    @13
    @27
    vc
    cE
    @28
    @9
    cE
    wcel
    #
    wa
    #
    @13
    @21
    @7
    @30
    @13
    wa
    #
    @21
    wa
    @6
    @12
    @20
    @5
    co
    #
    cS
    @13
    @21
    @6
    @32
    wceq
    @30
    cX
    @12
    cY
    @20
    @5
    oveq12
    adantll
    @31
    @32
    cS
    wcel
    #
    @21
    @30
    @33
    @13
    @30
    @32
    @9
    @19
    cR
    cmulr
    cfv
    #
    co
    #
    @10
    @11
    co
    #
    cS
    @30
    @2
    @29
    @25
    wa
    @32
    @36
    wceq
    @2
    @18
    @25
    @8
    @29
    simp-4l
    @30
    @25
    @29
    @28
    @25
    @29
    @24
    @25
    @8
    simplr
    anim1i
    ancomd
    cA
    cE
    cR
    @9
    @19
    @34
    @5
    @10
    @11
    cN
    c.0
    scmatid.a
    scmatid.e
    scmatid.0
    @16
    @17
    @34
    eqid
    #
    @5
    eqid
    scmatscmiddistr
    syl2anc
    @28
    @29
    @36
    cS
    wcel
    #
    @26
    @29
    @38
    wi
    #
    @8
    @24
    @25
    @39
    @2
    @25
    @39
    wi
    @18
    @2
    @25
    @29
    @38
    @2
    @25
    @29
    wa
    #
    wa
    #
    @38
    @36
    cB
    wcel
    #
    @36
    ve
    cv
    #
    @10
    @11
    co
    #
    wceq
    #
    ve
    cE
    wrex
    #
    @41
    @2
    @35
    cE
    wcel
    #
    @10
    cB
    wcel
    #
    @42
    @2
    @40
    simpl
    @41
    @1
    @29
    @25
    @47
    @0
    @1
    @40
    simplr
    @2
    @25
    @29
    simprr
    @40
    @25
    @2
    @25
    @29
    simpl
    adantl
    cE
    cR
    @34
    @9
    @19
    scmatid.e
    @37
    ringcl
    syl3anc
    #
    @2
    @48
    @40
    @2
    cA
    crg
    wcel
    @48
    cA
    cR
    cN
    scmatid.a
    matring
    cB
    cA
    @10
    scmatid.b
    @16
    ringidcl
    syl
    adantr
    cA
    cB
    @35
    cR
    @11
    cE
    cN
    @10
    scmatid.e
    scmatid.a
    scmatid.b
    @17
    matvscl
    syl12anc
    @41
    @45
    @36
    @36
    wceq
    #
    ve
    @35
    cE
    @49
    @43
    @35
    wceq
    #
    @45
    @50
    wb
    @41
    @51
    @44
    @36
    @36
    @43
    @35
    @10
    @11
    oveq1
    eqeq2d
    adantl
    @41
    @36
    eqidd
    rspcedvd
    @2
    @38
    @42
    @46
    wa
    wb
    @40
    cA
    cB
    cR
    cS
    @11
    @10
    cE
    @36
    cN
    crg
    ve
    scmatid.e
    scmatid.a
    scmatid.b
    @16
    @17
    scmatid.s
    scmatel
    adantr
    mpbir2and
    exp32
    adantr
    imp
    adantr
    imp
    eqeltrd
    adantr
    adantr
    eqeltrd
    exp31
    rexlimdva
    expimpd
    com23
    rexlimdva
    expimpd
    sylbid
    com23
    sylbid
    imp32
end
