include "cfv.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "ces.mm"
include "cmpl.mm"
include "cbs.mm"
include "cpws.mm"
include "wf.mm"
include "wcel.mm"
include "wceq.mm"
include "crh.mm"
include "con0.mm"
include "ccrg.mm"
include "csubrg.mm"
include "1on.mm"
include "a1i.mm"
include "eqid.mm"
include "evlsrhm.mm"
include "syl3anc.mm"
include "rhmf.mm"
include "syl.mm"
include "csca.mm"
include "crg.mm"
include "subrgring.mm"
include "ply1ring.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclf.mm"
include "wss.mm"
include "subrgss.mm"
include "ressbas2.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "cps1.mm"
include "ply1bas.mm"
include "eqcomd.mm"
include "feq23d.mm"
include "mpbird.mm"
include "ffvelrnd.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "cascl.mm"
include "ply1ascl.mm"
include "syl6eq.mm"
include "fveq1d.mm"
include "evlssca.mm"
include "cvv.mm"
include "eqidd.mm"
include "coeq1.mm"
include "adantl.mm"
include "sseldd.mm"
include "fconst6g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ovex.mm"
include "elmapd.mm"
include "snex.mm"
include "xpex.mm"
include "mptexg.mm"
include "coexg.mm"
include "fvmptd.mm"
include "wa.mm"
include "wb.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "fconstmpt.mm"
include "fmptco.mm"
include "3eqtrd.mm"
include "cpw.mm"
include "elpwg.mm"
include "evls1fval.mm"
include "3eqtr4d.mm"

theorem evls1sca
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume evls1sca.q: |- Q = ( S evalSub1 R )
  assume evls1sca.w: |- W = ( Poly1 ` U )
  assume evls1sca.u: |- U = ( S |`s R )
  assume evls1sca.b: |- B = ( Base ` S )
  assume evls1sca.a: |- A = ( algSc ` W )
  assume evls1sca.s: |- ( ph -> S e. CRing )
  assume evls1sca.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evls1sca.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( Q ` ( A ` X ) ) = ( B X. { X } ) )

  proof
    wph
    cX
    cA
    cfv
    #
    vx
    cB
    cB
    c1o
    cmap
    co
    #
    cmap
    co
    #
    vx
    cv
    #
    vy
    cB
    c1o
    vy
    cv
    #
    csn
    cxp
    #
    cmpt
    #
    ccom
    #
    cmpt
    #
    cR
    c1o
    cS
    ces
    co
    #
    cfv
    #
    ccom
    #
    cfv
    #
    vy
    cB
    cX
    cmpt
    #
    @0
    cQ
    cfv
    cB
    cX
    csn
    #
    cxp
    #
    wph
    @12
    @0
    @10
    cfv
    #
    @8
    cfv
    #
    @1
    @14
    cxp
    #
    @8
    cfv
    #
    @13
    wph
    c1o
    cU
    cmpl
    co
    #
    cbs
    cfv
    #
    cS
    @1
    cpws
    co
    #
    cbs
    cfv
    #
    @10
    wf
    #
    @0
    @21
    wcel
    @12
    @17
    wceq
    wph
    @10
    @20
    @22
    crh
    co
    wcel
    #
    @24
    wph
    c1o
    con0
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    #
    wcel
    #
    @25
    @26
    wph
    1on
    a1i
    #
    evls1sca.s
    evls1sca.r
    cB
    @10
    cR
    cS
    @22
    cU
    c1o
    con0
    @20
    @10
    eqid
    #
    @20
    eqid
    #
    evls1sca.u
    @22
    eqid
    evls1sca.b
    evlsrhm
    syl3anc
    @21
    @23
    @20
    @22
    @10
    @21
    eqid
    @23
    eqid
    rhmf
    syl
    wph
    cR
    @21
    cX
    cA
    wph
    cR
    @21
    cA
    wf
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cW
    cbs
    cfv
    #
    cA
    wf
    wph
    cA
    @35
    @33
    @34
    cW
    evls1sca.a
    @33
    eqid
    wph
    cU
    crg
    wcel
    #
    cW
    crg
    wcel
    wph
    @29
    @36
    evls1sca.r
    cR
    cS
    cU
    evls1sca.u
    subrgring
    syl
    #
    cW
    cU
    evls1sca.w
    ply1ring
    syl
    wph
    @36
    cW
    clmod
    wcel
    @37
    cW
    cU
    evls1sca.w
    ply1lmod
    syl
    @34
    eqid
    @35
    eqid
    #
    asclf
    wph
    cR
    @21
    @34
    @35
    cA
    wph
    cR
    cU
    cbs
    cfv
    #
    @34
    wph
    cR
    cB
    wss
    #
    cR
    @39
    wceq
    wph
    @29
    @40
    evls1sca.r
    cR
    cB
    cS
    evls1sca.b
    subrgss
    #
    syl
    #
    cR
    cB
    cU
    cS
    evls1sca.u
    evls1sca.b
    ressbas2
    syl
    wph
    cU
    @33
    cbs
    wph
    @36
    cU
    @33
    wceq
    @37
    cW
    cU
    crg
    evls1sca.w
    ply1sca
    syl
    fveq2d
    eqtrd
    wph
    @35
    @21
    @35
    @21
    wceq
    wph
    cW
    cU
    cU
    cps1
    cfv
    #
    @35
    evls1sca.w
    @43
    eqid
    @38
    ply1bas
    a1i
    eqcomd
    feq23d
    mpbird
    evls1sca.x
    ffvelrnd
    @21
    @23
    @0
    @8
    @10
    fvco3
    syl2anc
    wph
    @16
    @18
    @8
    wph
    @16
    cX
    @20
    cascl
    cfv
    #
    cfv
    #
    @10
    cfv
    @18
    wph
    @0
    @45
    @10
    wph
    cX
    cA
    @44
    wph
    cA
    cW
    cascl
    cfv
    #
    @44
    cA
    @46
    wceq
    wph
    evls1sca.a
    a1i
    @46
    cW
    cU
    evls1sca.w
    @46
    eqid
    ply1ascl
    syl6eq
    fveq1d
    fveq2d
    wph
    @44
    cB
    @10
    cR
    cS
    cU
    c1o
    con0
    @20
    cX
    @31
    @32
    evls1sca.u
    evls1sca.b
    @44
    eqid
    @30
    evls1sca.s
    evls1sca.r
    evls1sca.x
    evlssca
    eqtrd
    fveq2d
    wph
    @19
    @18
    @6
    ccom
    #
    @13
    wph
    vx
    @18
    @7
    @47
    @2
    @8
    cvv
    wph
    @8
    eqidd
    @3
    @18
    wceq
    @7
    @47
    wceq
    wph
    @3
    @18
    @6
    coeq1
    adantl
    wph
    @18
    @2
    wcel
    @1
    cB
    @18
    wf
    #
    wph
    cX
    cB
    wcel
    @48
    wph
    cR
    cB
    cX
    @42
    evls1sca.x
    sseldd
    @1
    cX
    cB
    fconst6g
    syl
    wph
    cB
    @1
    @18
    cvv
    cvv
    cB
    cvv
    wcel
    #
    wph
    cB
    cS
    cbs
    cfv
    cvv
    evls1sca.b
    cS
    cbs
    fvex
    eqeltri
    #
    a1i
    #
    @1
    cvv
    wcel
    wph
    cB
    c1o
    cmap
    ovex
    #
    a1i
    elmapd
    mpbird
    wph
    @18
    cvv
    wcel
    #
    @6
    cvv
    wcel
    #
    @47
    cvv
    wcel
    @53
    wph
    @1
    @14
    @52
    cX
    snex
    xpex
    a1i
    wph
    @49
    @54
    @51
    vy
    cB
    @5
    cvv
    mptexg
    syl
    @18
    @6
    cvv
    cvv
    coexg
    syl2anc
    fvmptd
    wph
    vy
    vz
    cB
    @1
    @5
    cX
    cX
    @6
    @18
    wph
    @4
    cB
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    #
    c1o
    cB
    @5
    wf
    #
    @55
    @58
    wph
    c1o
    @4
    cB
    fconst6g
    adantl
    @56
    @49
    @26
    wa
    #
    @57
    @58
    wb
    @59
    @56
    @49
    @26
    @50
    1on
    pm3.2i
    a1i
    cB
    c1o
    @5
    cvv
    con0
    elmapg
    syl
    mpbird
    wph
    @6
    eqidd
    @18
    vz
    @1
    cX
    cmpt
    wceq
    wph
    vz
    @1
    cX
    fconstmpt
    a1i
    vz
    cv
    @5
    wceq
    cX
    eqidd
    fmptco
    eqtrd
    3eqtrd
    wph
    @0
    cQ
    @11
    wph
    @27
    cR
    cB
    cpw
    wcel
    #
    cQ
    @11
    wceq
    evls1sca.s
    wph
    @29
    @60
    evls1sca.r
    @29
    @60
    @40
    @41
    cR
    cB
    @28
    elpwg
    mpbird
    syl
    vx
    vy
    cB
    cQ
    cR
    cS
    @9
    ccrg
    evls1sca.q
    @9
    eqid
    evls1sca.b
    evls1fval
    syl2anc
    fveq1d
    @15
    @13
    wceq
    wph
    vy
    cB
    cX
    fconstmpt
    a1i
    3eqtr4d
end
