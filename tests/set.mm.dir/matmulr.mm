include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cfrlm.mm"
include "co.mm"
include "cnx.mm"
include "cmulr.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cvv.mm"
include "wceq.mm"
include "ovex.mm"
include "cotp.mm"
include "cmmul.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "mulrid.mm"
include "setsid.mm"
include "mp1i.mm"
include "eqid.mm"
include "matval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem matmulr
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cV: class V
  assume matmulr.a: |- A = ( N Mat R )
  assume matmulr.t: |- .x. = ( R maMul <. N , N , N >. )


  assert |- ( ( N e. Fin /\ R e. V ) -> .x. = ( .r ` A ) )

  proof
    cN
    cfn
    wcel
    cR
    cV
    wcel
    wa
    #
    c.x
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    #
    cnx
    cmulr
    cfv
    c.x
    cop
    csts
    co
    #
    cmulr
    cfv
    #
    cA
    cmulr
    cfv
    @2
    cvv
    wcel
    #
    c.x
    cvv
    wcel
    #
    wa
    c.x
    @4
    wceq
    @0
    @5
    @6
    cR
    @1
    cfrlm
    ovex
    c.x
    cR
    cN
    cN
    cN
    cotp
    #
    cmmul
    co
    cvv
    matmulr.t
    cR
    @7
    cmmul
    ovex
    eqeltri
    pm3.2i
    cvv
    c.x
    cmulr
    cvv
    @2
    mulrid
    setsid
    mp1i
    @0
    cA
    @3
    cmulr
    cA
    cR
    c.x
    @2
    cN
    cV
    matmulr.a
    @2
    eqid
    matmulr.t
    matval
    fveq2d
    eqtr4d
end
