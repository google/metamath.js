include "cv.mm"
include "cfv.mm"
include "cds.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "fnex.mm"
include "syl2anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "prdsds.mm"
include "wa.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "uneq1d.mm"
include "supeq1d.mm"
include "xrltso.mm"
include "supex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem prdsdsval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
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
  assume prdsdsval.d: |- D = ( dist ` Y )

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
  assert |- ( ph -> ( F D G ) = sup ( ( ran ( x e. I |-> ( ( F ` x ) ( dist ` ( R ` x ) ) ( G ` x ) ) ) u. { 0 } ) , RR* , < ) )

  proof
    wph
    vf
    vg
    cF
    cG
    cB
    cB
    vx
    cI
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    @0
    vg
    cv
    #
    cfv
    #
    @0
    cR
    cfv
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
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
    crn
    #
    @9
    cun
    #
    cxr
    clt
    csup
    #
    cD
    cvv
    wph
    vx
    cB
    cD
    cY
    cR
    cS
    vf
    vg
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
    @18
    cR
    cdm
    cI
    wceq
    prdsbasmpt.r
    cI
    cR
    fndm
    syl
    prdsdsval.d
    prdsds
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
    #
    cxr
    @10
    @16
    clt
    @22
    @8
    @15
    @9
    @22
    @7
    @14
    @22
    vx
    cI
    @6
    @13
    @21
    @6
    @13
    wceq
    wph
    @19
    @20
    @2
    @11
    @4
    @12
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
    rneqd
    uneq1d
    supeq1d
    prdsplusgval.f
    prdsplusgval.g
    @17
    cvv
    wcel
    wph
    cxr
    @16
    clt
    xrltso
    supex
    a1i
    ovmpt2d
end
