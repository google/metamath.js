include "cmpt.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "cixp.mm"
include "wral.mm"
include "prdsbas2.mm"
include "eleq2d.mm"
include "wb.mm"
include "mptelixpg.mm"
include "syl.mm"
include "bitrd.mm"

theorem prdsbasmpt
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cT: class T
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsbasmpt.s: |- ( ph -> S e. V )
  assume prdsbasmpt.i: |- ( ph -> I e. W )
  assume prdsbasmpt.r: |- ( ph -> R Fn I )

  disjoint B x
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
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G g
  disjoint G x
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
  assert |- ( ph -> ( ( x e. I |-> U ) e. B <-> A. x e. I U e. ( Base ` ( R ` x ) ) ) )

  proof
    wph
    vx
    cI
    cU
    cmpt
    #
    cB
    wcel
    @0
    vx
    cI
    vx
    cv
    cR
    cfv
    cbs
    cfv
    #
    cixp
    #
    wcel
    #
    cU
    @1
    wcel
    vx
    cI
    wral
    #
    wph
    cB
    @2
    @0
    wph
    vx
    cB
    cR
    cS
    cI
    cV
    cW
    cY
    prdsbasmpt.y
    prdsbasmpt.b
    prdsbasmpt.s
    prdsbasmpt.i
    prdsbasmpt.r
    prdsbas2
    eleq2d
    wph
    cI
    cW
    wcel
    @3
    @4
    wb
    prdsbasmpt.i
    vx
    cI
    cU
    @1
    cW
    mptelixpg
    syl
    bitrd
end
