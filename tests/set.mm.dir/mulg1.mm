include "wcel.mm"
include "c1.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cn.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "wceq.mm"
include "1nn.mm"
include "eqid.mm"
include "mulgnn.mm"
include "mpan.mm"
include "1z.mm"
include "fvconst2g.mm"
include "mpan2.mm"
include "seq1i.mm"
include "eqtrd.mm"

theorem mulg1
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cX: class X
  assume mulg1.b: |- B = ( Base ` G )
  assume mulg1.m: |- .x. = ( .g ` G )


  assert |- ( X e. B -> ( 1 .x. X ) = X )

  proof
    cX
    cB
    wcel
    #
    c1
    cX
    c.x
    co
    #
    c1
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cX
    c1
    cn
    wcel
    #
    @0
    @1
    @5
    wceq
    1nn
    cB
    @2
    @4
    c.x
    cG
    c1
    cX
    mulg1.b
    @2
    eqid
    mulg1.m
    @4
    eqid
    mulgnn
    mpan
    @0
    cX
    @2
    @3
    c1
    1z
    @0
    @6
    c1
    @3
    cfv
    cX
    wceq
    1nn
    cn
    cX
    c1
    cB
    fvconst2g
    mpan2
    seq1i
    eqtrd
end
