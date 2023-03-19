include "cdiv.mm"
include "co.mm"
include "oveq2d.mm"
include "cmul.mm"
include "c1.mm"
include "cc.mm"
include "cclm.mm"
include "wcel.mm"
include "wss.mm"
include "cvsclm.mm"
include "clmsscn.mm"
include "syl.mm"
include "sseldd.mm"
include "divcan6d.mm"
include "oveq1d.mm"
include "wceq.mm"
include "ccvs.mm"
include "cc0.mm"
include "wne.mm"
include "cvsdivcl.mm"
include "syl13anc.mm"
include "clmvsass.mm"
include "clmvs1.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"

theorem cvsdiveqd
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
  assume cvsdiveqd.2: |- ( ph -> B =/= 0 )
  assume cvsdiveqd.3: |- ( ph -> X = ( ( A / B ) .x. Y ) )


  assert |- ( ph -> ( ( B / A ) .x. X ) = Y )

  proof
    wph
    cB
    cA
    cdiv
    co
    #
    cX
    c.x
    co
    @0
    cA
    cB
    cdiv
    co
    #
    cY
    c.x
    co
    #
    c.x
    co
    #
    cY
    wph
    cX
    @2
    @0
    c.x
    cvsdiveqd.3
    oveq2d
    wph
    @0
    @1
    cmul
    co
    #
    cY
    c.x
    co
    #
    c1
    cY
    c.x
    co
    #
    @3
    cY
    wph
    @4
    c1
    cY
    c.x
    wph
    cB
    cA
    wph
    cK
    cc
    cB
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
    cvsdiveqd.b
    sseldd
    wph
    cK
    cc
    cA
    @9
    cvsdiveqd.a
    sseldd
    cvsdiveqd.2
    cvsdiveqd.1
    divcan6d
    oveq1d
    wph
    @7
    @0
    cK
    wcel
    #
    @1
    cK
    wcel
    #
    cY
    cV
    wcel
    #
    @5
    @3
    wceq
    @8
    wph
    cW
    ccvs
    wcel
    #
    cB
    cK
    wcel
    #
    cA
    cK
    wcel
    #
    cA
    cc0
    wne
    @10
    cvsdiveqd.w
    cvsdiveqd.b
    cvsdiveqd.a
    cvsdiveqd.1
    cB
    cA
    cF
    cK
    cW
    cvsdiveqd.f
    cvsdiveqd.k
    cvsdivcl
    syl13anc
    wph
    @13
    @15
    @14
    cB
    cc0
    wne
    @11
    cvsdiveqd.w
    cvsdiveqd.a
    cvsdiveqd.b
    cvsdiveqd.2
    cA
    cB
    cF
    cK
    cW
    cvsdiveqd.f
    cvsdiveqd.k
    cvsdivcl
    syl13anc
    cvsdiveqd.y
    @0
    @1
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
    wph
    @7
    @12
    @6
    cY
    wceq
    @8
    cvsdiveqd.y
    c.x
    cV
    cW
    cY
    cvsdiveqd.v
    cvsdiveqd.t
    clmvs1
    syl2anc
    3eqtr3d
    eqtrd
end
