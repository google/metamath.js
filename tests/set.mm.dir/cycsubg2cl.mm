include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "csubg.mm"
include "co.mm"
include "cmre.mm"
include "wss.mm"
include "subgacs.mm"
include "acsmred.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "snssd.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "mrcssidd.mm"
include "wb.mm"
include "snssg.mm"
include "3ad2ant2.mm"
include "mpbird.mm"
include "subgmulgcl.mm"
include "syl3anc.mm"

theorem cycsubg2cl
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cK: class K
  let cN: class N
  let cX: class X
  assume cycsubg2cl.x: |- X = ( Base ` G )
  assume cycsubg2cl.t: |- .x. = ( .g ` G )
  assume cycsubg2cl.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ( G e. Grp /\ A e. X /\ N e. ZZ ) -> ( N .x. A ) e. ( K ` { A } ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    csn
    #
    cK
    cfv
    #
    cG
    csubg
    cfv
    #
    wcel
    #
    @2
    cA
    @5
    wcel
    #
    cN
    cA
    c.x
    co
    @5
    wcel
    @3
    @6
    cX
    cmre
    cfv
    wcel
    #
    @4
    cX
    wss
    @7
    @0
    @1
    @9
    @2
    @0
    @6
    cX
    cX
    cG
    cycsubg2cl.x
    subgacs
    acsmred
    3ad2ant1
    #
    @3
    cA
    cX
    @0
    @1
    @2
    simp2
    snssd
    #
    @6
    @4
    cK
    cX
    cycsubg2cl.k
    mrccl
    syl2anc
    @0
    @1
    @2
    simp3
    @3
    @8
    @4
    @5
    wss
    #
    @3
    @6
    @4
    cK
    cX
    @10
    cycsubg2cl.k
    @11
    mrcssidd
    @1
    @0
    @8
    @12
    wb
    @2
    cA
    @5
    cX
    snssg
    3ad2ant2
    mpbird
    @5
    c.x
    cG
    cN
    cA
    cycsubg2cl.t
    subgmulgcl
    syl3anc
end
