include "cv.mm"
include "cfv.mm"
include "cplusg.mm"
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
include "prdsplusg.mm"
include "wa.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "mptexg.mm"
include "ovmpt2d.mm"

theorem prdsplusgval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cK: class K
  let cT: class T
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsbasmpt.s: |- ( ph -> S e. V )
  assume prdsbasmpt.i: |- ( ph -> I e. W )
  assume prdsbasmpt.r: |- ( ph -> R Fn I )
  assume prdsplusgval.f: |- ( ph -> F e. B )
  assume prdsplusgval.g: |- ( ph -> G e. B )
  assume prdsplusgval.p: |- .+ = ( +g ` Y )

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
  assert |- ( ph -> ( F .+ G ) = ( x e. I |-> ( ( F ` x ) ( +g ` ( R ` x ) ) ( G ` x ) ) ) )

  proof
    wph
    vy
    vz
    cF
    cG
    cB
    cB
    vx
    cI
    vx
    cv
    #
    vy
    cv
    #
    cfv
    #
    @0
    vz
    cv
    #
    cfv
    #
    @0
    cR
    cfv
    cplusg
    cfv
    #
    co
    #
    cmpt
    vx
    cI
    @0
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    @5
    co
    #
    cmpt
    #
    c.pl
    cvv
    wph
    vx
    cB
    cY
    c.pl
    cR
    cS
    vy
    vz
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
    #
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
    @11
    cR
    cdm
    cI
    wceq
    prdsbasmpt.r
    cI
    cR
    fndm
    syl
    prdsplusgval.p
    prdsplusg
    wph
    @1
    cF
    wceq
    #
    @3
    cG
    wceq
    #
    wa
    #
    wa
    vx
    cI
    @6
    @9
    @15
    @6
    @9
    wceq
    wph
    @13
    @14
    @2
    @7
    @4
    @8
    @5
    @0
    @1
    cF
    fveq1
    @0
    @3
    cG
    fveq1
    oveqan12d
    adantl
    mpteq2dv
    prdsplusgval.f
    prdsplusgval.g
    wph
    @12
    @10
    cvv
    wcel
    prdsbasmpt.i
    vx
    cI
    @9
    cW
    mptexg
    syl
    ovmpt2d
end
