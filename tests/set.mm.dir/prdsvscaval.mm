include "cv.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "prdsvsca.mm"
include "wa.mm"
include "id.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "mptexg.mm"
include "ovmpt2d.mm"

theorem prdsvscaval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
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

  disjoint B x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint I x
  disjoint V x
  disjoint R x
  disjoint S x
  disjoint W x
  disjoint Y x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F g
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G y
  disjoint G z
  disjoint f ph
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint I f
  disjoint I g
  disjoint I y
  disjoint I z
  disjoint J x
  disjoint K y
  disjoint K z
  disjoint T x
  disjoint R f
  disjoint R g
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint S z
  disjoint Y f
  disjoint Y g
  disjoint Y y
  disjoint Y z
  assert |- ( ph -> ( F .x. G ) = ( x e. I |-> ( F ( .s ` ( R ` x ) ) ( G ` x ) ) ) )

  proof
    wph
    vy
    vz
    cF
    cG
    cK
    cB
    vx
    cI
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    cfv
    #
    @1
    cR
    cfv
    cvsca
    cfv
    #
    co
    #
    cmpt
    vx
    cI
    cF
    @1
    cG
    cfv
    #
    @4
    co
    #
    cmpt
    #
    c.x
    cvv
    wph
    vx
    cB
    cY
    cR
    cS
    c.x
    vy
    vz
    cI
    cK
    cV
    cvv
    prdsbasmpt.y
    prdsvscaval.s
    wph
    cR
    cI
    wfn
    #
    cI
    cW
    wcel
    #
    cR
    cvv
    wcel
    prdsvscaval.r
    prdsvscaval.i
    cI
    cW
    cR
    fnex
    syl2anc
    prdsbasmpt.b
    wph
    @9
    cR
    cdm
    cI
    wceq
    prdsvscaval.r
    cI
    cR
    fndm
    syl
    prdsvscaval.k
    prdsvscaval.t
    prdsvsca
    wph
    @0
    cF
    wceq
    #
    @2
    cG
    wceq
    #
    wa
    #
    wa
    vx
    cI
    @5
    @7
    @13
    @5
    @7
    wceq
    wph
    @11
    @12
    @0
    cF
    @3
    @6
    @4
    @11
    id
    @1
    @2
    cG
    fveq1
    oveqan12d
    adantl
    mpteq2dv
    prdsvscaval.f
    prdsvscaval.g
    wph
    @10
    @8
    cvv
    wcel
    prdsvscaval.i
    vx
    cI
    @7
    cW
    mptexg
    syl
    ovmpt2d
end
