include "cress.mm"
include "co.mm"
include "cmvr.mm"
include "cfv.mm"
include "ces.mm"
include "cmap.mm"
include "cv.mm"
include "cmpt.mm"
include "eqid.mm"
include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "evlsvarsrng.mm"
include "evlsvar.mm"
include "subrgmvr.mm"
include "fveq1d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "3eqtr3rd.mm"

theorem evlvar
  let wph: wff ph
  let cB: class B
  let cQ: class Q
  let cS: class S
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume evlvar.q: |- Q = ( I eval S )
  assume evlvar.v: |- V = ( I mVar S )
  assume evlvar.b: |- B = ( Base ` S )
  assume evlvar.i: |- ( ph -> I e. W )
  assume evlvar.s: |- ( ph -> S e. CRing )
  assume evlvar.x: |- ( ph -> X e. I )

  disjoint B g
  disjoint I g
  disjoint S g
  disjoint W g
  disjoint X g
  assert |- ( ph -> ( Q ` ( V ` X ) ) = ( g e. ( B ^m I ) |-> ( g ` X ) ) )

  proof
    wph
    cX
    cI
    cS
    cB
    cress
    co
    #
    cmvr
    co
    #
    cfv
    #
    cB
    cI
    cS
    ces
    co
    cfv
    #
    cfv
    @2
    cQ
    cfv
    vg
    cB
    cI
    cmap
    co
    cX
    vg
    cv
    cfv
    cmpt
    cX
    cV
    cfv
    #
    cQ
    cfv
    wph
    cW
    cB
    @3
    cB
    cS
    @0
    cI
    cQ
    @1
    cX
    @3
    eqid
    #
    evlvar.q
    @1
    eqid
    #
    @0
    eqid
    #
    evlvar.b
    evlvar.i
    evlvar.s
    wph
    cS
    ccrg
    wcel
    cS
    crg
    wcel
    cB
    cS
    csubrg
    cfv
    wcel
    evlvar.s
    cS
    crngring
    cB
    cS
    evlvar.b
    subrgid
    3syl
    #
    evlvar.x
    evlsvarsrng
    wph
    cB
    @3
    cB
    cS
    @0
    vg
    cI
    @1
    cW
    cX
    @5
    @6
    @7
    evlvar.b
    evlvar.i
    evlvar.s
    @8
    evlvar.x
    evlsvar
    wph
    @2
    @4
    cQ
    wph
    @4
    @2
    wph
    cX
    cV
    @1
    wph
    cS
    cB
    @0
    cI
    cV
    cW
    evlvar.v
    evlvar.i
    @8
    @7
    subrgmvr
    fveq1d
    eqcomd
    fveq2d
    3eqtr3rd
end
