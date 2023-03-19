include "cclm.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "csca.mm"
include "eqid.mm"
include "clmvneg1.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "wceq.mm"
include "clmgrp.mm"
include "grprinv.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem clmvsrinv
  let cA: class A
  let c.pl: class .+
  let c.x: class .x.
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume clmpm1dir.v: |- V = ( Base ` W )
  assume clmpm1dir.s: |- .x. = ( .s ` W )
  assume clmpm1dir.a: |- .+ = ( +g ` W )
  assume clmvsrinv.0: |- .0. = ( 0g ` W )


  assert |- ( ( W e. CMod /\ A e. V ) -> ( A .+ ( -u 1 .x. A ) ) = .0. )

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
    cA
    c1
    cneg
    cA
    c.x
    co
    #
    c.pl
    co
    cA
    cA
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    c.0
    @2
    @3
    @5
    cA
    c.pl
    c.x
    cW
    csca
    cfv
    #
    @4
    cV
    cW
    cA
    clmpm1dir.v
    @4
    eqid
    #
    @7
    eqid
    clmpm1dir.s
    clmvneg1
    oveq2d
    @0
    cW
    cgrp
    wcel
    @1
    @6
    c.0
    wceq
    cW
    clmgrp
    cV
    c.pl
    cW
    @4
    cA
    c.0
    clmpm1dir.v
    clmpm1dir.a
    clmvsrinv.0
    @8
    grprinv
    sylan
    eqtrd
end
