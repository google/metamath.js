include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "evlsvar.mm"
include "ces.mm"
include "cress.mm"
include "cmvr.mm"
include "wceq.mm"
include "evlval.mm"
include "a1i.mm"
include "fveq1d.mm"
include "eqid.mm"
include "subrgmvr.mm"
include "ccrg.mm"
include "wcel.mm"
include "ressid.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "3eqtrrd.mm"
include "eqtrd.mm"

theorem evlsvarsrng
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cO: class O
  let cV: class V
  let cX: class X
  let vg: setvar g
  assume evlsvarsrng.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsvarsrng.o: |- O = ( I eval S )
  assume evlsvarsrng.v: |- V = ( I mVar U )
  assume evlsvarsrng.u: |- U = ( S |`s R )
  assume evlsvarsrng.b: |- B = ( Base ` S )
  assume evlsvarsrng.i: |- ( ph -> I e. A )
  assume evlsvarsrng.s: |- ( ph -> S e. CRing )
  assume evlsvarsrng.r: |- ( ph -> R e. ( SubRing ` S ) )
  assume evlsvarsrng.x: |- ( ph -> X e. I )


  assert |- ( ph -> ( Q ` ( V ` X ) ) = ( O ` ( V ` X ) ) )

  proof
    wph
    cX
    cV
    cfv
    #
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
    #
    @0
    cO
    cfv
    #
    wph
    cB
    cQ
    cR
    cS
    cU
    vg
    cI
    cV
    cA
    cX
    evlsvarsrng.q
    evlsvarsrng.v
    evlsvarsrng.u
    evlsvarsrng.b
    evlsvarsrng.i
    evlsvarsrng.s
    evlsvarsrng.r
    evlsvarsrng.x
    evlsvar
    wph
    @2
    @0
    cB
    cI
    cS
    ces
    co
    cfv
    #
    cfv
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
    @3
    cfv
    @1
    wph
    @0
    cO
    @3
    cO
    @3
    wceq
    wph
    cB
    cO
    cS
    cI
    evlsvarsrng.o
    evlsvarsrng.b
    evlval
    a1i
    fveq1d
    wph
    @0
    @6
    @3
    wph
    cX
    cV
    @5
    wph
    cV
    cI
    cU
    cmvr
    co
    #
    cI
    cS
    cmvr
    co
    #
    @5
    cV
    @7
    wceq
    wph
    evlsvarsrng.v
    a1i
    wph
    cS
    cR
    cU
    cI
    @8
    cA
    @8
    eqid
    evlsvarsrng.i
    evlsvarsrng.r
    evlsvarsrng.u
    subrgmvr
    wph
    cS
    @4
    cI
    cmvr
    wph
    @4
    cS
    wph
    cS
    ccrg
    wcel
    #
    @4
    cS
    wceq
    evlsvarsrng.s
    cB
    cS
    ccrg
    evlsvarsrng.b
    ressid
    syl
    eqcomd
    oveq2d
    3eqtr2d
    fveq1d
    fveq2d
    wph
    cB
    @3
    cB
    cS
    @4
    vg
    cI
    @5
    cA
    cX
    @3
    eqid
    @5
    eqid
    @4
    eqid
    evlsvarsrng.b
    evlsvarsrng.i
    evlsvarsrng.s
    wph
    @9
    cS
    crg
    wcel
    cB
    cS
    csubrg
    cfv
    wcel
    evlsvarsrng.s
    cS
    crngring
    cB
    cS
    evlsvarsrng.b
    subrgid
    3syl
    evlsvarsrng.x
    evlsvar
    3eqtrrd
    eqtrd
end
