include "cv.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "cvv.mm"
include "prdsvscaval.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "adantl.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem prdsvscafval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsvscaval.t: |- .x. = ( .s ` Y )
  assume prdsvscaval.k: |- K = ( Base ` S )
  assume prdsvscaval.s: |- ( ph -> S e. V )
  assume prdsvscaval.i: |- ( ph -> I e. W )
  assume prdsvscaval.r: |- ( ph -> R Fn I )
  assume prdsvscaval.f: |- ( ph -> F e. K )
  assume prdsvscaval.g: |- ( ph -> G e. B )
  assume prdsvscafval.j: |- ( ph -> J e. I )


  assert |- ( ph -> ( ( F .x. G ) ` J ) = ( F ( .s ` ( R ` J ) ) ( G ` J ) ) )

  proof
    wph
    vx
    cJ
    cF
    vx
    cv
    #
    cG
    cfv
    #
    @0
    cR
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cF
    cJ
    cG
    cfv
    #
    cJ
    cR
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cI
    cF
    cG
    c.x
    co
    cvv
    wph
    vx
    cB
    cR
    cS
    c.x
    cF
    cG
    cI
    cK
    cV
    cW
    cY
    prdsbasmpt.y
    prdsbasmpt.b
    prdsvscaval.t
    prdsvscaval.k
    prdsvscaval.s
    prdsvscaval.i
    prdsvscaval.r
    prdsvscaval.f
    prdsvscaval.g
    prdsvscaval
    @0
    cJ
    wceq
    #
    @4
    @8
    wceq
    wph
    @9
    cF
    cF
    @1
    @5
    @3
    @7
    @9
    @2
    @6
    cvsca
    @0
    cJ
    cR
    fveq2
    fveq2d
    @9
    cF
    eqidd
    @0
    cJ
    cG
    fveq2
    oveq123d
    adantl
    prdsvscafval.j
    wph
    cF
    @5
    @7
    ovexd
    fvmptd
end
