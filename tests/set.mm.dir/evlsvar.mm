include "ccom.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cmpl.mm"
include "cpws.mm"
include "crh.mm"
include "wcel.mm"
include "cascl.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "ccrg.mm"
include "csubrg.mm"
include "wa.mm"
include "eqid.mm"
include "evlsval2.mm"
include "syl3anc.mm"
include "simprrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "cbs.mm"
include "crg.mm"
include "subrgring.mm"
include "syl.mm"
include "mvrf2.mm"
include "ffnd.mm"
include "fvco2.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "ovex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "3eqtr3d.mm"

theorem evlsvar
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume evlsvar.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsvar.v: |- V = ( I mVar U )
  assume evlsvar.u: |- U = ( S |`s R )
  assume evlsvar.b: |- B = ( Base ` S )
  assume evlsvar.i: |- ( ph -> I e. W )
  assume evlsvar.s: |- ( ph -> S e. CRing )
  assume evlsvar.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evlsvar.x: |- ( ph -> X e. I )

  disjoint B g
  disjoint I g
  disjoint R g
  disjoint S g
  disjoint W g
  disjoint X g
  disjoint B x
  disjoint g x
  disjoint I x
  disjoint R x
  disjoint S x
  disjoint W x
  disjoint X x
  assert |- ( ph -> ( Q ` ( V ` X ) ) = ( g e. ( B ^m I ) |-> ( g ` X ) ) )

  proof
    wph
    cX
    cQ
    cV
    ccom
    #
    cfv
    #
    cX
    vx
    cI
    vg
    cB
    cI
    cmap
    co
    #
    vx
    cv
    #
    vg
    cv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cX
    cV
    cfv
    cQ
    cfv
    #
    vg
    @2
    cX
    @4
    cfv
    #
    cmpt
    #
    wph
    cX
    @0
    @7
    wph
    cQ
    cI
    cU
    cmpl
    co
    #
    cS
    @2
    cpws
    co
    #
    crh
    co
    wcel
    #
    cQ
    @12
    cascl
    cfv
    #
    ccom
    vx
    cR
    @2
    @3
    csn
    cxp
    cmpt
    #
    wceq
    #
    @0
    @7
    wceq
    #
    wph
    cI
    cW
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
    @14
    @17
    @18
    wa
    wa
    evlsvar.i
    evlsvar.s
    evlsvar.r
    vx
    @15
    cB
    cQ
    cR
    cS
    @13
    cU
    vg
    cI
    cV
    @12
    @16
    @7
    cW
    evlsvar.q
    @12
    eqid
    #
    evlsvar.v
    evlsvar.u
    @13
    eqid
    evlsvar.b
    @15
    eqid
    @16
    eqid
    @7
    eqid
    #
    evlsval2
    syl3anc
    simprrd
    fveq1d
    wph
    cV
    cI
    wfn
    cX
    cI
    wcel
    #
    @1
    @9
    wceq
    wph
    cI
    @12
    cbs
    cfv
    #
    cV
    wph
    @23
    @12
    cU
    cI
    cV
    cW
    @20
    evlsvar.v
    @23
    eqid
    evlsvar.i
    wph
    @19
    cU
    crg
    wcel
    evlsvar.r
    cR
    cS
    cU
    evlsvar.u
    subrgring
    syl
    mvrf2
    ffnd
    evlsvar.x
    cI
    cQ
    cV
    cX
    fvco2
    syl2anc
    wph
    @22
    @8
    @11
    wceq
    evlsvar.x
    vx
    cX
    @6
    @11
    cI
    @7
    @3
    cX
    wceq
    vg
    @2
    @5
    @10
    @3
    cX
    @4
    fveq2
    mpteq2dv
    @21
    vg
    @2
    @10
    cB
    cI
    cmap
    ovex
    mptex
    fvmpt
    syl
    3eqtr3d
end
