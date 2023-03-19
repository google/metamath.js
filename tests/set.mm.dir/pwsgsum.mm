include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "ccmn.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "pwsval.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cvv.mm"
include "c0g.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "fvexd.mm"
include "cv.mm"
include "adantr.mm"
include "cfsupp.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "prdsgsum.mm"
include "eqtrd.mm"

theorem pwsgsum
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  assume pwsgsum.y: |- Y = ( R ^s I )
  assume pwsgsum.b: |- B = ( Base ` R )
  assume pwsgsum.z: |- .0. = ( 0g ` Y )
  assume pwsgsum.i: |- ( ph -> I e. V )
  assume pwsgsum.j: |- ( ph -> J e. W )
  assume pwsgsum.r: |- ( ph -> R e. CMnd )
  assume pwsgsum.f: |- ( ( ph /\ ( x e. I /\ y e. J ) ) -> U e. B )
  assume pwsgsum.w: |- ( ph -> ( y e. J |-> ( x e. I |-> U ) ) finSupp .0. )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint I x
  disjoint I y
  disjoint ph x
  disjoint ph y
  disjoint .0. x
  disjoint .0. y
  disjoint J x
  disjoint J y
  disjoint R x
  disjoint R y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( Y gsum ( y e. J |-> ( x e. I |-> U ) ) ) = ( x e. I |-> ( R gsum ( y e. J |-> U ) ) ) )

  proof
    wph
    cY
    vy
    cJ
    vx
    cI
    cU
    cmpt
    cmpt
    #
    cgsu
    co
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    @0
    cgsu
    co
    vx
    cI
    cR
    vy
    cJ
    cU
    cmpt
    cgsu
    co
    cmpt
    wph
    cY
    @3
    @0
    cgsu
    wph
    cR
    ccmn
    wcel
    #
    cI
    cV
    wcel
    cY
    @3
    wceq
    pwsgsum.r
    pwsgsum.i
    cR
    @1
    cI
    ccmn
    cV
    cY
    pwsgsum.y
    @1
    eqid
    pwsval
    syl2anc
    #
    oveq1d
    wph
    vx
    vy
    cB
    cR
    @1
    cU
    cI
    cJ
    cV
    cW
    cvv
    @3
    @3
    c0g
    cfv
    #
    @2
    vx
    cI
    cR
    cmpt
    @1
    cprds
    vx
    cI
    cR
    fconstmpt
    oveq2i
    pwsgsum.b
    @6
    eqid
    pwsgsum.i
    pwsgsum.j
    wph
    cR
    csca
    fvexd
    wph
    @4
    vx
    cv
    cI
    wcel
    pwsgsum.r
    adantr
    pwsgsum.f
    wph
    @0
    c.0
    @6
    cfsupp
    pwsgsum.w
    wph
    c.0
    cY
    c0g
    cfv
    @6
    pwsgsum.z
    wph
    cY
    @3
    c0g
    @5
    fveq2d
    syl5eq
    breqtrd
    prdsgsum
    eqtrd
end
