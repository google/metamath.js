include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "ces1.mm"
include "wceq.mm"
include "evl1fval1.mm"
include "a1i.mm"
include "fveq1d.mm"
include "cress.mm"
include "cpl1.mm"
include "ccrg.mm"
include "wcel.mm"
include "ressid.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "crg.mm"
include "csubrg.mm"
include "crngring.mm"
include "subrgid.mm"
include "3syl.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "cfsupp.mm"
include "syl6eqr.mm"
include "breqtrrd.mm"
include "evls1gsumadd.mm"
include "eqtrd.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem evl1gsumadd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cK: class K
  let cN: class N
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  assume evl1gsumadd.q: |- Q = ( eval1 ` R )
  assume evl1gsumadd.k: |- K = ( Base ` R )
  assume evl1gsumadd.w: |- W = ( Poly1 ` R )
  assume evl1gsumadd.p: |- P = ( R ^s K )
  assume evl1gsumadd.b: |- B = ( Base ` W )
  assume evl1gsumadd.r: |- ( ph -> R e. CRing )
  assume evl1gsumadd.y: |- ( ( ph /\ x e. N ) -> Y e. B )
  assume evl1gsumadd.n: |- ( ph -> N C_ NN0 )
  assume evl1gsumadd.0: |- .0. = ( 0g ` W )
  assume evl1gsumadd.f: |- ( ph -> ( x e. N |-> Y ) finSupp .0. )

  disjoint B x
  disjoint K x
  disjoint N x
  disjoint Q x
  disjoint R x
  disjoint ph x
  assert |- ( ph -> ( Q ` ( W gsum ( x e. N |-> Y ) ) ) = ( P gsum ( x e. N |-> ( Q ` Y ) ) ) )

  proof
    wph
    cW
    vx
    cN
    cY
    cmpt
    #
    cgsu
    co
    #
    cQ
    cfv
    @1
    cR
    cK
    ces1
    co
    #
    cfv
    #
    cP
    vx
    cN
    cY
    @2
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    cP
    vx
    cN
    cY
    cQ
    cfv
    #
    cmpt
    #
    cgsu
    co
    wph
    @1
    cQ
    @2
    cQ
    @2
    wceq
    wph
    cK
    cQ
    cR
    evl1gsumadd.q
    evl1gsumadd.k
    evl1fval1
    a1i
    #
    fveq1d
    wph
    @3
    cR
    cK
    cress
    co
    #
    cpl1
    cfv
    #
    @0
    cgsu
    co
    #
    @2
    cfv
    @6
    wph
    @1
    @12
    @2
    wph
    cW
    @11
    @0
    cgsu
    wph
    cW
    cR
    cpl1
    cfv
    @11
    evl1gsumadd.w
    wph
    cR
    @10
    cpl1
    wph
    @10
    cR
    wph
    cR
    ccrg
    wcel
    #
    @10
    cR
    wceq
    evl1gsumadd.r
    cK
    cR
    ccrg
    evl1gsumadd.k
    ressid
    syl
    eqcomd
    fveq2d
    syl5eq
    #
    oveq1d
    fveq2d
    wph
    vx
    @11
    cbs
    cfv
    #
    cP
    @2
    cK
    cR
    @10
    cK
    cN
    @11
    cY
    @11
    c0g
    cfv
    #
    @2
    eqid
    evl1gsumadd.k
    @11
    eqid
    @16
    eqid
    @10
    eqid
    evl1gsumadd.p
    @15
    eqid
    evl1gsumadd.r
    wph
    @13
    cR
    crg
    wcel
    cK
    cR
    csubrg
    cfv
    wcel
    evl1gsumadd.r
    cR
    crngring
    cK
    cR
    evl1gsumadd.k
    subrgid
    3syl
    wph
    vx
    cv
    cN
    wcel
    #
    wa
    #
    cY
    cB
    @15
    evl1gsumadd.y
    @18
    cB
    cW
    cbs
    cfv
    @15
    evl1gsumadd.b
    @18
    cW
    @11
    cbs
    wph
    cW
    @11
    wceq
    @17
    @14
    adantr
    fveq2d
    syl5eq
    eleqtrd
    evl1gsumadd.n
    wph
    @0
    c.0
    @16
    cfsupp
    evl1gsumadd.f
    wph
    @16
    cW
    c0g
    cfv
    c.0
    wph
    @11
    cW
    c0g
    wph
    cW
    @11
    @14
    eqcomd
    fveq2d
    evl1gsumadd.0
    syl6eqr
    breqtrrd
    evls1gsumadd
    eqtrd
    wph
    @5
    @8
    cP
    cgsu
    wph
    vx
    cN
    @4
    @7
    wph
    @7
    @4
    wph
    cY
    cQ
    @2
    @9
    fveq1d
    eqcomd
    mpteq2dv
    oveq2d
    3eqtrd
end
