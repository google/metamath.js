include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cple.mm"
include "wral.mm"
include "copab.mm"
include "df-br.mm"
include "cpr.mm"
include "wss.mm"
include "cvv.mm"
include "wfn.mm"
include "fnex.mm"
include "syl2anc.mm"
include "cdm.mm"
include "wceq.mm"
include "fndm.mm"
include "syl.mm"
include "prdsle.mm"
include "vex.mm"
include "prss.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "wb.mm"
include "fveq1.mm"
include "breqan12d.mm"
include "ralbidv.mm"
include "opelopab2a.mm"
include "bitrd.mm"

theorem prdsleval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cI: class I
  let c.le: class .<_
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
  assume prdsleval.l: |- .<_ = ( le ` Y )

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
  assert |- ( ph -> ( F .<_ G <-> A. x e. I ( F ` x ) ( le ` ( R ` x ) ) ( G ` x ) ) )

  proof
    wph
    cF
    cG
    c.le
    wbr
    #
    cF
    cG
    cop
    #
    vf
    cv
    #
    cB
    wcel
    vg
    cv
    #
    cB
    wcel
    wa
    #
    vx
    cv
    #
    @2
    cfv
    #
    @5
    @3
    cfv
    #
    @5
    cR
    cfv
    cple
    cfv
    #
    wbr
    #
    vx
    cI
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    wcel
    #
    @5
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    @8
    wbr
    #
    vx
    cI
    wral
    #
    @0
    @1
    c.le
    wcel
    wph
    @13
    cF
    cG
    c.le
    df-br
    wph
    c.le
    @12
    @1
    wph
    c.le
    @2
    @3
    cpr
    cB
    wss
    #
    @10
    wa
    #
    vf
    vg
    copab
    @12
    wph
    vx
    cB
    cY
    cR
    cS
    vf
    vg
    cI
    c.le
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
    @20
    cR
    cdm
    cI
    wceq
    prdsbasmpt.r
    cI
    cR
    fndm
    syl
    prdsleval.l
    prdsle
    @11
    @19
    vf
    vg
    @4
    @18
    @10
    @2
    @3
    cB
    vf
    vex
    vg
    vex
    prss
    anbi1i
    opabbii
    syl6eqr
    eleq2d
    syl5bb
    wph
    cF
    cB
    wcel
    cG
    cB
    wcel
    @13
    @17
    wb
    prdsplusgval.f
    prdsplusgval.g
    @10
    @17
    vf
    vg
    cF
    cG
    cB
    cB
    @2
    cF
    wceq
    #
    @3
    cG
    wceq
    #
    wa
    @9
    @16
    vx
    cI
    @21
    @22
    @6
    @14
    @7
    @15
    @8
    @5
    @2
    cF
    fveq1
    @5
    @3
    cG
    fveq1
    breqan12d
    ralbidv
    opelopab2a
    syl2anc
    bitrd
end
