include "cple.mm"
include "cfv.mm"
include "ccnv.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "cnvex.mm"
include "pleid.mm"
include "setsid.mm"
include "mpan2.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "cnveqd.mm"
include "cnv0.mm"
include "syl6eq.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "cnveqi.mm"
include "eqid.mm"
include "oduval.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem oduleval
  let cD: class D
  let c.le: class .<_
  let cO: class O
  let va: setvar a
  let cG: class G
  let cA: class A
  let cB: class B
  assume oduval.d: |- D = ( ODual ` O )
  assume oduval.l: |- .<_ = ( le ` O )


  assert |- `' .<_ = ( le ` D )

  proof
    cO
    cple
    cfv
    #
    ccnv
    #
    cO
    cnx
    cple
    cfv
    #
    @1
    cop
    #
    csts
    co
    #
    cple
    cfv
    #
    c.le
    ccnv
    cD
    cple
    cfv
    cO
    cvv
    wcel
    #
    @1
    @5
    wceq
    #
    @6
    @1
    cvv
    wcel
    @7
    @0
    cO
    cple
    fvex
    cnvex
    cvv
    @1
    cple
    cvv
    cO
    pleid
    setsid
    mpan2
    @6
    wn
    #
    c0
    c0
    cple
    cfv
    @1
    @5
    cple
    @2
    pleid
    str0
    @8
    @1
    c0
    ccnv
    c0
    @8
    @0
    c0
    cO
    cple
    fvprc
    cnveqd
    cnv0
    syl6eq
    @8
    @4
    c0
    cple
    cO
    @3
    csts
    reldmsets
    ovprc1
    fveq2d
    3eqtr4a
    pm2.61i
    c.le
    @0
    oduval.l
    cnveqi
    cD
    @4
    cple
    cD
    @0
    cO
    oduval.d
    @0
    eqid
    oduval
    fveq2i
    3eqtr4i
end
