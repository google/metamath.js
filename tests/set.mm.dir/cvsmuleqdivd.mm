include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "oveq2d.mm"
include "cmul.mm"
include "cc.mm"
include "cclm.mm"
include "wcel.mm"
include "wss.mm"
include "cvsclm.mm"
include "clmsscn.mm"
include "syl.mm"
include "sseldd.mm"
include "recid2d.mm"
include "oveq1d.mm"
include "wceq.mm"
include "ccvs.mm"
include "cc0.mm"
include "wne.mm"
include "cur.mm"
include "cfv.mm"
include "clm1.mm"
include "crg.mm"
include "clmring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "cvsdivcl.mm"
include "syl13anc.mm"
include "clmvsass.mm"
include "clmvs1.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "divrec2d.mm"
include "eqtr2d.mm"

theorem cvsmuleqdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume cvsdiveqd.v: |- V = ( Base ` W )
  assume cvsdiveqd.t: |- .x. = ( .s ` W )
  assume cvsdiveqd.f: |- F = ( Scalar ` W )
  assume cvsdiveqd.k: |- K = ( Base ` F )
  assume cvsdiveqd.w: |- ( ph -> W e. CVec )
  assume cvsdiveqd.a: |- ( ph -> A e. K )
  assume cvsdiveqd.b: |- ( ph -> B e. K )
  assume cvsdiveqd.x: |- ( ph -> X e. V )
  assume cvsdiveqd.y: |- ( ph -> Y e. V )
  assume cvsdiveqd.1: |- ( ph -> A =/= 0 )
  assume cvsmuleqdivd.1: |- ( ph -> ( A .x. X ) = ( B .x. Y ) )


  assert |- ( ph -> X = ( ( B / A ) .x. Y ) )

  proof
    wph
    c1
    cA
    cdiv
    co
    #
    cA
    cX
    c.x
    co
    #
    c.x
    co
    #
    @0
    cB
    cY
    c.x
    co
    #
    c.x
    co
    #
    cX
    cB
    cA
    cdiv
    co
    #
    cY
    c.x
    co
    #
    wph
    @1
    @3
    @0
    c.x
    cvsmuleqdivd.1
    oveq2d
    wph
    @0
    cA
    cmul
    co
    #
    cX
    c.x
    co
    #
    c1
    cX
    c.x
    co
    #
    @2
    cX
    wph
    @7
    c1
    cX
    c.x
    wph
    cA
    wph
    cK
    cc
    cA
    wph
    cW
    cclm
    wcel
    #
    cK
    cc
    wss
    wph
    cW
    cvsdiveqd.w
    cvsclm
    #
    cF
    cK
    cW
    cvsdiveqd.f
    cvsdiveqd.k
    clmsscn
    syl
    #
    cvsdiveqd.a
    sseldd
    #
    cvsdiveqd.1
    recid2d
    oveq1d
    wph
    @10
    @0
    cK
    wcel
    #
    cA
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    @8
    @2
    wceq
    @11
    wph
    cW
    ccvs
    wcel
    c1
    cK
    wcel
    @15
    cA
    cc0
    wne
    @14
    cvsdiveqd.w
    wph
    c1
    cF
    cur
    cfv
    #
    cK
    wph
    @10
    c1
    @17
    wceq
    @11
    cF
    cW
    cvsdiveqd.f
    clm1
    syl
    wph
    @10
    cF
    crg
    wcel
    @17
    cK
    wcel
    @11
    cF
    cW
    cvsdiveqd.f
    clmring
    cK
    cF
    @17
    cvsdiveqd.k
    @17
    eqid
    ringidcl
    3syl
    eqeltrd
    cvsdiveqd.a
    cvsdiveqd.1
    c1
    cA
    cF
    cK
    cW
    cvsdiveqd.f
    cvsdiveqd.k
    cvsdivcl
    syl13anc
    #
    cvsdiveqd.a
    cvsdiveqd.x
    @0
    cA
    c.x
    cF
    cK
    cV
    cW
    cX
    cvsdiveqd.v
    cvsdiveqd.f
    cvsdiveqd.t
    cvsdiveqd.k
    clmvsass
    syl13anc
    wph
    @10
    @16
    @9
    cX
    wceq
    @11
    cvsdiveqd.x
    c.x
    cV
    cW
    cX
    cvsdiveqd.v
    cvsdiveqd.t
    clmvs1
    syl2anc
    3eqtr3d
    wph
    @6
    @0
    cB
    cmul
    co
    #
    cY
    c.x
    co
    #
    @4
    wph
    @5
    @19
    cY
    c.x
    wph
    cB
    cA
    wph
    cK
    cc
    cB
    @12
    cvsdiveqd.b
    sseldd
    @13
    cvsdiveqd.1
    divrec2d
    oveq1d
    wph
    @10
    @14
    cB
    cK
    wcel
    cY
    cV
    wcel
    @20
    @4
    wceq
    @11
    @18
    cvsdiveqd.b
    cvsdiveqd.y
    @0
    cB
    c.x
    cF
    cK
    cV
    cW
    cY
    cvsdiveqd.v
    cvsdiveqd.f
    cvsdiveqd.t
    cvsdiveqd.k
    clmvsass
    syl13anc
    eqtr2d
    3eqtr3d
end
