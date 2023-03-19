include "codu.mm"
include "cfv.mm"
include "cnx.mm"
include "cple.mm"
include "ccnv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "cnveqd.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-odu.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "cnveqi.mm"
include "opeq2i.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem oduval
  let cD: class D
  let c.le: class .<_
  let cO: class O
  let va: setvar a
  let cG: class G
  let cA: class A
  let cB: class B
  assume oduval.d: |- D = ( ODual ` O )
  assume oduval.l: |- .<_ = ( le ` O )


  assert |- D = ( O sSet <. ( le ` ndx ) , `' .<_ >. )

  proof
    cO
    codu
    cfv
    #
    cO
    cnx
    cple
    cfv
    #
    cO
    cple
    cfv
    #
    ccnv
    #
    cop
    #
    csts
    co
    #
    cD
    cO
    @1
    c.le
    ccnv
    #
    cop
    #
    csts
    co
    cO
    cvv
    wcel
    #
    @0
    @5
    wceq
    va
    cO
    va
    cv
    #
    @1
    @9
    cple
    cfv
    #
    ccnv
    #
    cop
    #
    csts
    co
    @5
    cvv
    codu
    @9
    cO
    wceq
    #
    @9
    cO
    @12
    @4
    csts
    @13
    id
    @13
    @11
    @3
    @1
    @13
    @10
    @2
    @9
    cO
    cple
    fveq2
    cnveqd
    opeq2d
    oveq12d
    va
    df-odu
    cO
    @4
    csts
    ovex
    fvmpt
    @8
    wn
    @0
    c0
    @5
    cO
    codu
    fvprc
    cO
    @4
    csts
    reldmsets
    ovprc1
    eqtr4d
    pm2.61i
    oduval.d
    @7
    @4
    cO
    csts
    @6
    @3
    @1
    c.le
    @2
    oduval.l
    cnveqi
    opeq2i
    oveq2i
    3eqtr4i
end
