include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cq.mm"
include "cv.mm"
include "cnumer.mm"
include "cdenom.mm"
include "co.mm"
include "cqqh.mm"
include "cvv.mm"
include "cmpt.mm"
include "qqhval2.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem qqhvval
  let cB: class B
  let c.dv: class ./
  let cQ: class Q
  let cR: class R
  let cL: class L
  let ve: setvar e
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )


  assert |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ Q e. QQ ) -> ( ( QQHom ` R ) ` Q ) = ( ( L ` ( numer ` Q ) ) ./ ( L ` ( denom ` Q ) ) ) )

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
    cQ
    cq
    wcel
    #
    wa
    #
    vq
    cQ
    vq
    cv
    #
    cnumer
    cfv
    #
    cL
    cfv
    #
    @3
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cQ
    cnumer
    cfv
    #
    cL
    cfv
    #
    cQ
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    cq
    cR
    cqqh
    cfv
    #
    cvv
    @0
    @13
    vq
    cq
    @8
    cmpt
    wceq
    @1
    cB
    c.dv
    cR
    cL
    vq
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhval2
    adantr
    @2
    @3
    cQ
    wceq
    #
    wa
    #
    @5
    @10
    @7
    @12
    c.dv
    @15
    @4
    @9
    cL
    @15
    @3
    cQ
    cnumer
    @2
    @14
    simpr
    #
    fveq2d
    fveq2d
    @15
    @6
    @11
    cL
    @15
    @3
    cQ
    cdenom
    @16
    fveq2d
    fveq2d
    oveq12d
    @0
    @1
    simpr
    @2
    @10
    @12
    c.dv
    ovexd
    fvmptd
end
