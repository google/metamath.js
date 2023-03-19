include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "wceq.mm"
include "simpl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "id.mm"
include "peano2nn.mm"
include "fvconst2g.mm"
include "syl2anr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqid.mm"
include "mulgnn.mm"
include "sylan.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem mulgnnp1
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  assume mulg1.b: |- B = ( Base ` G )
  assume mulg1.m: |- .x. = ( .g ` G )
  assume mulgnnp1.p: |- .+ = ( +g ` G )


  assert |- ( ( N e. NN /\ X e. B ) -> ( ( N + 1 ) .x. X ) = ( ( N .x. X ) .+ X ) )

  proof
    cN
    cn
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cN
    c1
    caddc
    co
    #
    c.pl
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
    cN
    @5
    cfv
    #
    cX
    c.pl
    co
    #
    @3
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cX
    c.pl
    co
    @2
    @6
    @7
    @3
    @4
    cfv
    #
    c.pl
    co
    #
    @8
    @2
    cN
    c1
    cuz
    cfv
    #
    wcel
    @6
    @12
    wceq
    @2
    cN
    cn
    @13
    @0
    @1
    simpl
    nnuz
    syl6eleq
    c.pl
    @4
    c1
    cN
    seqp1
    syl
    @2
    @11
    cX
    @7
    c.pl
    @1
    @1
    @3
    cn
    wcel
    #
    @11
    cX
    wceq
    @0
    @1
    id
    cN
    peano2nn
    #
    cn
    cX
    @3
    cB
    fvconst2g
    syl2anr
    oveq2d
    eqtrd
    @0
    @14
    @1
    @9
    @6
    wceq
    @15
    cB
    c.pl
    @5
    c.x
    cG
    @3
    cX
    mulg1.b
    mulgnnp1.p
    mulg1.m
    @5
    eqid
    #
    mulgnn
    sylan
    @2
    @10
    @7
    cX
    c.pl
    cB
    c.pl
    @5
    c.x
    cG
    cN
    cX
    mulg1.b
    mulgnnp1.p
    mulg1.m
    @16
    mulgnn
    oveq1d
    3eqtr4d
end
