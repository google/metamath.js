include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cminusg.mm"
include "wceq.mm"
include "cbs.mm"
include "cz.mm"
include "eqid.mm"
include "clmzss.mm"
include "1zzd.mm"
include "sseldd.mm"
include "clmneg.mm"
include "mpdan.mm"
include "clm1.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "adantr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "clmlmod.mm"
include "lmodvneg1.mm"
include "sylan.mm"

theorem clmvneg1
  let c.x: class .x.
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmvneg1.v: |- V = ( Base ` W )
  assume clmvneg1.n: |- N = ( invg ` W )
  assume clmvneg1.f: |- F = ( Scalar ` W )
  assume clmvneg1.s: |- .x. = ( .s ` W )


  assert |- ( ( W e. CMod /\ X e. V ) -> ( -u 1 .x. X ) = ( N ` X ) )

  proof
    cW
    cclm
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    c1
    cneg
    #
    cX
    c.x
    co
    cF
    cur
    cfv
    #
    cF
    cminusg
    cfv
    #
    cfv
    #
    cX
    c.x
    co
    #
    cX
    cN
    cfv
    #
    @2
    @3
    @6
    cX
    c.x
    @0
    @3
    @6
    wceq
    @1
    @0
    @3
    c1
    @5
    cfv
    #
    @6
    @0
    c1
    cF
    cbs
    cfv
    #
    wcel
    @3
    @9
    wceq
    @0
    cz
    @10
    c1
    cF
    @10
    cW
    clmvneg1.f
    @10
    eqid
    #
    clmzss
    @0
    1zzd
    sseldd
    c1
    cF
    @10
    cW
    clmvneg1.f
    @11
    clmneg
    mpdan
    @0
    c1
    @4
    @5
    cF
    cW
    clmvneg1.f
    clm1
    fveq2d
    eqtrd
    adantr
    oveq1d
    @0
    cW
    clmod
    wcel
    @1
    @7
    @8
    wceq
    cW
    clmlmod
    c.x
    @4
    cF
    @5
    cN
    cV
    cW
    cX
    clmvneg1.v
    clmvneg1.n
    clmvneg1.f
    clmvneg1.s
    @4
    eqid
    @5
    eqid
    lmodvneg1
    sylan
    eqtrd
end
