include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cqqh.mm"
include "cnumer.mm"
include "cdenom.mm"
include "cq.mm"
include "zssq.mm"
include "simpr1.mm"
include "sseldi.mm"
include "simpr2.mm"
include "simpr3.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "qqhvval.mm"
include "syldan.mm"
include "qqhval2lem.mm"
include "eqtrd.mm"

theorem qqhvq
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cL: class L
  let cX: class X
  let cY: class Y
  let ve: setvar e
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cQ: class Q
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )


  assert |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ ( X e. ZZ /\ Y e. ZZ /\ Y =/= 0 ) ) -> ( ( QQHom ` R ) ` ( X / Y ) ) = ( ( L ` X ) ./ ( L ` Y ) ) )

  proof
    cR
    cdr
    wcel
    cR
    cchr
    cfv
    cc0
    wceq
    wa
    #
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    cY
    cc0
    wne
    #
    w3a
    #
    wa
    #
    cX
    cY
    cdiv
    co
    #
    cR
    cqqh
    cfv
    cfv
    #
    @6
    cnumer
    cfv
    cL
    cfv
    @6
    cdenom
    cfv
    cL
    cfv
    c.dv
    co
    #
    cX
    cL
    cfv
    cY
    cL
    cfv
    c.dv
    co
    @0
    @4
    @6
    cq
    wcel
    #
    @7
    @8
    wceq
    @5
    cX
    cq
    wcel
    cY
    cq
    wcel
    @3
    @9
    @5
    cz
    cq
    cX
    zssq
    @0
    @1
    @2
    @3
    simpr1
    sseldi
    @5
    cz
    cq
    cY
    zssq
    @0
    @1
    @2
    @3
    simpr2
    sseldi
    @0
    @1
    @2
    @3
    simpr3
    cX
    cY
    qdivcl
    syl3anc
    cB
    c.dv
    @6
    cR
    cL
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhvval
    syldan
    cB
    c.dv
    cR
    cL
    cX
    cY
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhval2lem
    eqtrd
end
