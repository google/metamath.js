include "cn0.mm"
include "wcel.mm"
include "cmnd.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "co.mm"
include "elnn0.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "id.mm"
include "mndidcl.mm"
include "eqid.mm"
include "mulgnn.mm"
include "syl2anr.mm"
include "mndlid.mm"
include "mpdan.mm"
include "adantr.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cv.mm"
include "cfz.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "seqid3.mm"
include "eqtrd.mm"
include "oveq1.mm"
include "mulg0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem mulgnn0z
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  assume mulgnn0z.b: |- B = ( Base ` G )
  assume mulgnn0z.t: |- .x. = ( .g ` G )
  assume mulgnn0z.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Mnd /\ N e. NN0 ) -> ( N .x. .0. ) = .0. )

  proof
    cN
    cn0
    wcel
    cG
    cmnd
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cN
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    cN
    elnn0
    @0
    @1
    @4
    @2
    @0
    @1
    wa
    #
    @3
    cN
    cG
    cplusg
    cfv
    #
    cn
    c.0
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    c.0
    @1
    @1
    c.0
    cB
    wcel
    #
    @3
    @9
    wceq
    @0
    @1
    id
    cB
    cG
    c.0
    mulgnn0z.b
    mulgnn0z.o
    mndidcl
    #
    cB
    @6
    @8
    c.x
    cG
    cN
    c.0
    mulgnn0z.b
    @6
    eqid
    #
    mulgnn0z.t
    @8
    eqid
    mulgnn
    syl2anr
    @5
    vx
    @6
    @7
    c1
    cN
    c.0
    @0
    c.0
    c.0
    @6
    co
    c.0
    wceq
    #
    @1
    @0
    @10
    @13
    @11
    cB
    @6
    cG
    c.0
    c.0
    mulgnn0z.b
    @12
    mulgnn0z.o
    mndlid
    mpdan
    adantr
    @5
    cN
    cn
    c1
    cuz
    cfv
    @0
    @1
    simpr
    nnuz
    syl6eleq
    @5
    @10
    vx
    cv
    #
    cn
    wcel
    @14
    @7
    cfv
    c.0
    wceq
    @14
    c1
    cN
    cfz
    co
    wcel
    @0
    @10
    @1
    @11
    adantr
    @14
    cN
    elfznn
    cn
    c.0
    @14
    cB
    fvconst2g
    syl2an
    seqid3
    eqtrd
    @2
    @0
    @3
    cc0
    c.0
    c.x
    co
    #
    c.0
    cN
    cc0
    c.0
    c.x
    oveq1
    @0
    @10
    @15
    c.0
    wceq
    @11
    cB
    c.x
    cG
    c.0
    c.0
    mulgnn0z.b
    mulgnn0z.o
    mulgnn0z.t
    mulg0
    syl
    sylan9eqr
    jaodan
    sylan2b
end
