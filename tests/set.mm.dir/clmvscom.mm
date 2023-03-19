include "cclm.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "ssel.mm"
include "anim12d.mm"
include "clmsscn.mm"
include "syl11.mm"
include "3adant3.mm"
include "impcom.mm"
include "mulcom.mm"
include "syl.mm"
include "oveq1d.mm"
include "clmvsass.mm"
include "3ancoma.mm"
include "sylan2b.mm"
include "3eqtr3d.mm"

theorem clmvscom
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmvscl.v: |- V = ( Base ` W )
  assume clmvscl.f: |- F = ( Scalar ` W )
  assume clmvscl.s: |- .x. = ( .s ` W )
  assume clmvscl.k: |- K = ( Base ` F )


  assert |- ( ( W e. CMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) -> ( Q .x. ( R .x. X ) ) = ( R .x. ( Q .x. X ) ) )

  proof
    cW
    cclm
    wcel
    #
    cQ
    cK
    wcel
    #
    cR
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cQ
    cR
    cmul
    co
    #
    cX
    c.x
    co
    cR
    cQ
    cmul
    co
    #
    cX
    c.x
    co
    #
    cQ
    cR
    cX
    c.x
    co
    c.x
    co
    cR
    cQ
    cX
    c.x
    co
    c.x
    co
    #
    @5
    @6
    @7
    cX
    c.x
    @5
    cQ
    cc
    wcel
    #
    cR
    cc
    wcel
    #
    wa
    #
    @6
    @7
    wceq
    @4
    @0
    @12
    @1
    @2
    @0
    @12
    wi
    @3
    cK
    cc
    wss
    #
    @1
    @2
    wa
    @12
    @0
    @13
    @1
    @10
    @2
    @11
    cK
    cc
    cQ
    ssel
    cK
    cc
    cR
    ssel
    anim12d
    cF
    cK
    cW
    clmvscl.f
    clmvscl.k
    clmsscn
    syl11
    3adant3
    impcom
    cQ
    cR
    mulcom
    syl
    oveq1d
    cQ
    cR
    c.x
    cF
    cK
    cV
    cW
    cX
    clmvscl.v
    clmvscl.f
    clmvscl.s
    clmvscl.k
    clmvsass
    @4
    @0
    @2
    @1
    @3
    w3a
    @8
    @9
    wceq
    @1
    @2
    @3
    3ancoma
    cR
    cQ
    c.x
    cF
    cK
    cV
    cW
    cX
    clmvscl.v
    clmvscl.f
    clmvscl.s
    clmvscl.k
    clmvsass
    sylan2b
    3eqtr3d
end
