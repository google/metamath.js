include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "prdsmulrval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq123d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem prdsmulrfval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cT: class T
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsbasmpt.s: |- ( ph -> S e. V )
  assume prdsbasmpt.i: |- ( ph -> I e. W )
  assume prdsbasmpt.r: |- ( ph -> R Fn I )
  assume prdsplusgval.f: |- ( ph -> F e. B )
  assume prdsplusgval.g: |- ( ph -> G e. B )
  assume prdsmulrval.t: |- .x. = ( .r ` Y )
  assume prdsmulrfval.j: |- ( ph -> J e. I )


  assert |- ( ph -> ( ( F .x. G ) ` J ) = ( ( F ` J ) ( .r ` ( R ` J ) ) ( G ` J ) ) )

  proof
    wph
    cJ
    cF
    cG
    c.x
    co
    #
    cfv
    cJ
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    @1
    cR
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cfv
    #
    cJ
    cF
    cfv
    #
    cJ
    cG
    cfv
    #
    cJ
    cR
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    wph
    cJ
    @0
    @7
    wph
    vx
    cB
    cR
    cS
    c.x
    cF
    cG
    cI
    cV
    cW
    cY
    prdsbasmpt.y
    prdsbasmpt.b
    prdsbasmpt.s
    prdsbasmpt.i
    prdsbasmpt.r
    prdsplusgval.f
    prdsplusgval.g
    prdsmulrval.t
    prdsmulrval
    fveq1d
    wph
    cJ
    cI
    wcel
    @8
    @13
    wceq
    prdsmulrfval.j
    vx
    cJ
    @6
    @13
    cI
    @7
    @1
    cJ
    wceq
    #
    @2
    @9
    @3
    @10
    @5
    @12
    @14
    @4
    @11
    cmulr
    @1
    cJ
    cR
    fveq2
    fveq2d
    @1
    cJ
    cF
    fveq2
    @1
    cJ
    cG
    fveq2
    oveq123d
    @7
    eqid
    @9
    @10
    @12
    ovex
    fvmpt
    syl
    eqtrd
end
