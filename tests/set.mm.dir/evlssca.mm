include "ccom.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cpws.mm"
include "crh.mm"
include "wcel.mm"
include "wceq.mm"
include "cmvr.mm"
include "ccrg.mm"
include "csubrg.mm"
include "wa.mm"
include "eqid.mm"
include "evlsval2.mm"
include "syl3anc.mm"
include "simprld.mm"
include "fveq1d.mm"
include "cbs.mm"
include "wf.mm"
include "crg.mm"
include "subrgring.mm"
include "syl.mm"
include "mplasclf.mm"
include "wss.mm"
include "subrgss.mm"
include "ressbas2.mm"
include "3syl.mm"
include "feq2d.mm"
include "mpbird.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "ovex.mm"
include "snex.mm"
include "xpex.mm"
include "fvmpt.mm"
include "3eqtr3d.mm"

theorem evlssca
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume evlssca.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlssca.w: |- W = ( I mPoly U )
  assume evlssca.u: |- U = ( S |`s R )
  assume evlssca.b: |- B = ( Base ` S )
  assume evlssca.a: |- A = ( algSc ` W )
  assume evlssca.i: |- ( ph -> I e. V )
  assume evlssca.s: |- ( ph -> S e. CRing )
  assume evlssca.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evlssca.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( Q ` ( A ` X ) ) = ( ( B ^m I ) X. { X } ) )

  proof
    wph
    cX
    cQ
    cA
    ccom
    #
    cfv
    #
    cX
    vx
    cR
    cB
    cI
    cmap
    co
    #
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    cfv
    #
    cX
    cA
    cfv
    cQ
    cfv
    #
    @2
    cX
    csn
    #
    cxp
    #
    wph
    cX
    @0
    @6
    wph
    cQ
    cW
    cS
    @2
    cpws
    co
    #
    crh
    co
    wcel
    #
    @0
    @6
    wceq
    #
    cQ
    cI
    cU
    cmvr
    co
    #
    ccom
    vx
    cI
    vy
    @2
    @3
    vy
    cv
    cfv
    cmpt
    cmpt
    #
    wceq
    #
    wph
    cI
    cV
    wcel
    cS
    ccrg
    wcel
    cR
    cS
    csubrg
    cfv
    wcel
    #
    @12
    @13
    @16
    wa
    wa
    evlssca.i
    evlssca.s
    evlssca.r
    vx
    cA
    cB
    cQ
    cR
    cS
    @11
    cU
    vy
    cI
    @14
    cW
    @6
    @15
    cV
    evlssca.q
    evlssca.w
    @14
    eqid
    evlssca.u
    @11
    eqid
    evlssca.b
    evlssca.a
    @6
    eqid
    #
    @15
    eqid
    evlsval2
    syl3anc
    simprld
    fveq1d
    wph
    cR
    cW
    cbs
    cfv
    #
    cA
    wf
    #
    cX
    cR
    wcel
    #
    @1
    @8
    wceq
    wph
    @20
    cU
    cbs
    cfv
    #
    @19
    cA
    wf
    wph
    cA
    @19
    cW
    cU
    cI
    @22
    cV
    evlssca.w
    @19
    eqid
    @22
    eqid
    evlssca.a
    evlssca.i
    wph
    @17
    cU
    crg
    wcel
    evlssca.r
    cR
    cS
    cU
    evlssca.u
    subrgring
    syl
    mplasclf
    wph
    cR
    @22
    @19
    cA
    wph
    @17
    cR
    cB
    wss
    cR
    @22
    wceq
    evlssca.r
    cR
    cB
    cS
    evlssca.b
    subrgss
    cR
    cB
    cU
    cS
    evlssca.u
    evlssca.b
    ressbas2
    3syl
    feq2d
    mpbird
    evlssca.x
    cR
    @19
    cX
    cQ
    cA
    fvco3
    syl2anc
    wph
    @21
    @7
    @10
    wceq
    evlssca.x
    vx
    cX
    @5
    @10
    cR
    @6
    @3
    cX
    wceq
    @4
    @9
    @2
    @3
    cX
    sneq
    xpeq2d
    @18
    @2
    @9
    cB
    cI
    cmap
    ovex
    cX
    snex
    xpex
    fvmpt
    syl
    3eqtr3d
end
