include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cmgp.mm"
include "cmnd.mm"
include "cn0.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "ply1ring.mm"
include "eqid.mm"
include "ringmgp.mm"
include "3syl.mm"
include "simpld.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "cpws.mm"
include "cmg.mm"
include "cmhm.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmmhm.mm"
include "mhmmulg.mm"
include "cbs.mm"
include "cvv.mm"
include "eqidd.mm"
include "cplusg.mm"
include "wa.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwsmgp.mm"
include "sylancl.mm"
include "wss.mm"
include "ssv.mm"
include "a1i.mm"
include "cv.mm"
include "ovexd.mm"
include "simprd.mm"
include "oveqdr.mm"
include "mulgpropd.mm"
include "oveqd.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "wf.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "pwsmulg.mm"
include "syl23anc.mm"
include "oveq2d.mm"
include "jca.mm"

theorem evl1expd
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let cU: class U
  let c.ex: class .^
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume evl1addd.q: |- O = ( eval1 ` R )
  assume evl1addd.p: |- P = ( Poly1 ` R )
  assume evl1addd.b: |- B = ( Base ` R )
  assume evl1addd.u: |- U = ( Base ` P )
  assume evl1addd.1: |- ( ph -> R e. CRing )
  assume evl1addd.2: |- ( ph -> Y e. B )
  assume evl1addd.3: |- ( ph -> ( M e. U /\ ( ( O ` M ) ` Y ) = V ) )
  assume evl1expd.f: |- .xb = ( .g ` ( mulGrp ` P ) )
  assume evl1expd.e: |- .^ = ( .g ` ( mulGrp ` R ) )
  assume evl1expd.4: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( ( N .xb M ) e. U /\ ( ( O ` ( N .xb M ) ) ` Y ) = ( N .^ V ) ) )

  proof
    wph
    cN
    cM
    c.xb
    co
    #
    cU
    wcel
    #
    cY
    @0
    cO
    cfv
    #
    cfv
    #
    cN
    cV
    c.ex
    co
    #
    wceq
    wph
    cP
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    cN
    cn0
    wcel
    #
    cM
    cU
    wcel
    #
    @1
    wph
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    @6
    wph
    cR
    ccrg
    wcel
    #
    @9
    evl1addd.1
    cR
    crngring
    syl
    #
    cP
    cR
    evl1addd.p
    ply1ring
    cP
    @5
    @5
    eqid
    #
    ringmgp
    3syl
    evl1expd.4
    wph
    @8
    cY
    cM
    cO
    cfv
    #
    cfv
    #
    cV
    wceq
    #
    evl1addd.3
    simpld
    #
    cU
    c.xb
    @5
    cN
    cM
    cU
    cP
    @5
    @12
    evl1addd.u
    mgpbas
    #
    evl1expd.f
    mulgnn0cl
    syl3anc
    wph
    @3
    cY
    cN
    @13
    cR
    cmgp
    cfv
    #
    cB
    cpws
    co
    #
    cmg
    cfv
    #
    co
    #
    cfv
    #
    @4
    wph
    cY
    @2
    @21
    wph
    @2
    cN
    @13
    cR
    cB
    cpws
    co
    #
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @21
    wph
    cO
    @5
    @24
    cmhm
    co
    wcel
    #
    @7
    @8
    @2
    @26
    wceq
    wph
    cO
    cP
    @23
    crh
    co
    wcel
    #
    @27
    wph
    @10
    @28
    evl1addd.1
    cB
    cP
    cR
    @23
    cO
    evl1addd.q
    evl1addd.p
    @23
    eqid
    #
    evl1addd.b
    evl1rhm
    syl
    #
    cP
    @23
    cO
    @5
    @24
    @12
    @24
    eqid
    #
    rhmmhm
    syl
    evl1expd.4
    @16
    cU
    c.xb
    @25
    cO
    @5
    @24
    cN
    cM
    @17
    evl1expd.f
    @25
    eqid
    #
    mhmmulg
    syl3anc
    wph
    @25
    @20
    cN
    @13
    wph
    vx
    vy
    @24
    cbs
    cfv
    #
    @25
    @20
    @24
    @19
    cvv
    @32
    @20
    eqid
    #
    wph
    @33
    eqidd
    wph
    @33
    @19
    cbs
    cfv
    #
    wceq
    #
    @24
    cplusg
    cfv
    #
    @19
    cplusg
    cfv
    #
    wceq
    #
    wph
    @10
    cB
    cvv
    wcel
    #
    @36
    @39
    wa
    evl1addd.1
    cB
    cR
    cbs
    cfv
    cvv
    evl1addd.b
    cR
    cbs
    fvex
    eqeltri
    #
    @33
    @35
    @37
    @38
    cR
    cB
    @18
    @24
    ccrg
    cvv
    @23
    @19
    @29
    @18
    eqid
    #
    @19
    eqid
    #
    @31
    @33
    eqid
    @35
    eqid
    #
    @37
    eqid
    @38
    eqid
    pwsmgp
    sylancl
    #
    simpld
    #
    @33
    cvv
    wss
    wph
    @33
    ssv
    a1i
    wph
    vx
    cv
    #
    cvv
    wcel
    vy
    cv
    #
    cvv
    wcel
    wa
    #
    wa
    @47
    @48
    @37
    ovexd
    wph
    @49
    vx
    vy
    @37
    @38
    wph
    @36
    @39
    @45
    simprd
    oveqdr
    mulgpropd
    oveqd
    eqtrd
    fveq1d
    wph
    @22
    cN
    @14
    c.ex
    co
    #
    @4
    wph
    @18
    cmnd
    wcel
    #
    @40
    @7
    @13
    @35
    wcel
    cY
    cB
    wcel
    @22
    @50
    wceq
    wph
    @9
    @51
    @11
    cR
    @18
    @42
    ringmgp
    syl
    @40
    wph
    @41
    a1i
    evl1expd.4
    wph
    @13
    @23
    cbs
    cfv
    #
    @35
    wph
    cU
    @52
    cM
    cO
    wph
    @28
    cU
    @52
    cO
    wf
    @30
    cU
    @52
    cP
    @23
    cO
    evl1addd.u
    @52
    eqid
    #
    rhmf
    syl
    @16
    ffvelrnd
    wph
    @52
    @33
    @35
    @52
    @23
    @24
    @31
    @53
    mgpbas
    @46
    syl5eq
    eleqtrd
    evl1addd.2
    cY
    @35
    @18
    @20
    c.ex
    cB
    cN
    cvv
    @13
    @19
    @43
    @44
    @34
    evl1expd.e
    pwsmulg
    syl23anc
    wph
    @14
    cV
    cN
    c.ex
    wph
    @8
    @15
    evl1addd.3
    simprd
    oveq2d
    eqtrd
    eqtrd
    jca
end
