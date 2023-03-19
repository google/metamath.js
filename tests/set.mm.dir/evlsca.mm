include "cress.mm"
include "co.mm"
include "cmpl.mm"
include "cascl.mm"
include "cfv.mm"
include "ces.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "ccrg.mm"
include "wcel.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "evlsscasrng.mm"
include "evlssca.mm"
include "eqtr3d.mm"

theorem evlsca
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume evlsca.q: |- Q = ( I eval S )
  assume evlsca.w: |- W = ( I mPoly S )
  assume evlsca.b: |- B = ( Base ` S )
  assume evlsca.a: |- A = ( algSc ` W )
  assume evlsca.i: |- ( ph -> I e. V )
  assume evlsca.s: |- ( ph -> S e. CRing )
  assume evlsca.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( Q ` ( A ` X ) ) = ( ( B ^m I ) X. { X } ) )

  proof
    wph
    cX
    cI
    cS
    cB
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    cfv
    cB
    cI
    cS
    ces
    co
    cfv
    #
    cfv
    cX
    cA
    cfv
    cQ
    cfv
    cB
    cI
    cmap
    co
    cX
    csn
    cxp
    wph
    @2
    cB
    cA
    cW
    @3
    cB
    cS
    @0
    cI
    cQ
    cV
    @1
    cX
    @3
    eqid
    #
    evlsca.q
    @1
    eqid
    #
    @0
    eqid
    #
    evlsca.w
    evlsca.b
    @2
    eqid
    #
    evlsca.a
    evlsca.i
    evlsca.s
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
    evlsca.s
    cS
    crngring
    cB
    cS
    evlsca.b
    subrgid
    3syl
    #
    evlsca.x
    evlsscasrng
    wph
    @2
    cB
    @3
    cB
    cS
    @0
    cI
    cV
    @1
    cX
    @4
    @5
    @6
    evlsca.b
    @7
    evlsca.i
    evlsca.s
    @8
    evlsca.x
    evlssca
    eqtr3d
end
