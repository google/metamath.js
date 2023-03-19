include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "cgrp.mm"
include "clmgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "csca.mm"
include "eqid.mm"
include "clmvsubval2.mm"
include "syl3anc.mm"
include "cbs.mm"
include "clmneg1.mm"
include "clmvscl.mm"
include "grprid.mm"
include "syl2an2r.mm"
include "eqtrd.mm"

theorem clmvz
  let cA: class A
  let c.x: class .x.
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume clmvz.v: |- V = ( Base ` W )
  assume clmvz.m: |- .- = ( -g ` W )
  assume clmvz.s: |- .x. = ( .s ` W )
  assume clmvz.0: |- .0. = ( 0g ` W )


  assert |- ( ( W e. CMod /\ A e. V ) -> ( .0. .- A ) = ( -u 1 .x. A ) )

  proof
    cW
    cclm
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    c.0
    cA
    c.mi
    co
    #
    c1
    cneg
    #
    cA
    c.x
    co
    #
    c.0
    cW
    cplusg
    cfv
    #
    co
    #
    @5
    @2
    @0
    c.0
    cV
    wcel
    #
    @1
    @3
    @7
    wceq
    @0
    @1
    simpl
    #
    @0
    @8
    @1
    @0
    cW
    cgrp
    wcel
    #
    @8
    cW
    clmgrp
    #
    cV
    cW
    c.0
    clmvz.v
    clmvz.0
    grpidcl
    syl
    adantr
    @0
    @1
    simpr
    #
    c.0
    cA
    @6
    c.x
    cW
    csca
    cfv
    #
    c.mi
    cV
    cW
    clmvz.v
    @6
    eqid
    #
    clmvz.m
    @13
    eqid
    #
    clmvz.s
    clmvsubval2
    syl3anc
    @0
    @10
    @1
    @5
    cV
    wcel
    #
    @7
    @5
    wceq
    @11
    @2
    @0
    @4
    @13
    cbs
    cfv
    #
    wcel
    #
    @1
    @16
    @9
    @0
    @18
    @1
    @13
    @17
    cW
    @15
    @17
    eqid
    #
    clmneg1
    adantr
    @12
    @4
    c.x
    @13
    @17
    cV
    cW
    cA
    clmvz.v
    @15
    clmvz.s
    @19
    clmvscl
    syl3anc
    cV
    @6
    cW
    @5
    c.0
    clmvz.v
    @14
    clmvz.0
    grprid
    syl2an2r
    eqtrd
end
