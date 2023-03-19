include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "prdsbas.mm"

theorem prdsbas2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
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
  assert |- ( ph -> B = X_ x e. I ( Base ` ( R ` x ) ) )

  proof
    wph
    vx
    cB
    cY
    cR
    cS
    cI
    cV
    cvv
    prdsbasmpt.y
    prdsbasmpt.s
    wph
    cR
    cI
    wfn
    #
    cI
    cW
    wcel
    cR
    cvv
    wcel
    prdsbasmpt.r
    prdsbasmpt.i
    cI
    cW
    cR
    fnex
    syl2anc
    prdsbasmpt.b
    wph
    @0
    cR
    cdm
    cI
    wceq
    prdsbasmpt.r
    cI
    cR
    fndm
    syl
    prdsbas
end
