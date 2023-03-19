include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "wceq.mm"
include "uc1pcl.mm"
include "eqid.mm"
include "r1pval.mm"
include "sylan2.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "cabl.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "ringabl.mm"
include "syl.mm"
include "q1pcl.mm"
include "3ad2ant3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "simp2.mm"
include "grpsubcl.mm"
include "ablcom.mm"
include "grpnpcan.mm"
include "3eqtrrd.mm"

theorem r1pid
  let cB: class B
  let cC: class C
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cG: class G
  assume r1pid.p: |- P = ( Poly1 ` R )
  assume r1pid.b: |- B = ( Base ` P )
  assume r1pid.c: |- C = ( Unic1p ` R )
  assume r1pid.q: |- Q = ( quot1p ` R )
  assume r1pid.e: |- E = ( rem1p ` R )
  assume r1pid.t: |- .x. = ( .r ` P )
  assume r1pid.m: |- .+ = ( +g ` P )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> F = ( ( ( F Q G ) .x. G ) .+ ( F E G ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cC
    wcel
    #
    w3a
    #
    cF
    cG
    cQ
    co
    #
    cG
    c.x
    co
    #
    cF
    cG
    cE
    co
    #
    c.pl
    co
    @5
    cF
    @5
    cP
    csg
    cfv
    #
    co
    #
    c.pl
    co
    #
    @8
    @5
    c.pl
    co
    #
    cF
    @3
    @6
    @8
    @5
    c.pl
    @1
    @2
    @6
    @8
    wceq
    #
    @0
    @2
    @1
    cG
    cB
    wcel
    #
    @11
    cB
    cC
    cP
    cR
    cG
    r1pid.p
    r1pid.b
    r1pid.c
    uc1pcl
    #
    cB
    cP
    cQ
    cR
    c.x
    cE
    cF
    cG
    @7
    r1pid.e
    r1pid.p
    r1pid.b
    r1pid.q
    r1pid.t
    @7
    eqid
    #
    r1pval
    sylan2
    3adant1
    oveq2d
    @3
    cP
    cabl
    wcel
    #
    @5
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    @9
    @10
    wceq
    @3
    cP
    crg
    wcel
    #
    @15
    @0
    @1
    @18
    @2
    cP
    cR
    r1pid.p
    ply1ring
    3ad2ant1
    #
    cP
    ringabl
    syl
    @3
    @18
    @4
    cB
    wcel
    @12
    @16
    @19
    cB
    cC
    cP
    cQ
    cR
    cF
    cG
    r1pid.q
    r1pid.p
    r1pid.b
    r1pid.c
    q1pcl
    @2
    @0
    @12
    @1
    @13
    3ad2ant3
    cB
    cP
    c.x
    @4
    cG
    r1pid.b
    r1pid.t
    ringcl
    syl3anc
    #
    @3
    cP
    cgrp
    wcel
    #
    @1
    @16
    @17
    @3
    @18
    @21
    @19
    cP
    ringgrp
    syl
    #
    @0
    @1
    @2
    simp2
    #
    @20
    cB
    cP
    @7
    cF
    @5
    r1pid.b
    @14
    grpsubcl
    syl3anc
    cB
    c.pl
    cP
    @5
    @8
    r1pid.b
    r1pid.m
    ablcom
    syl3anc
    @3
    @21
    @1
    @16
    @10
    cF
    wceq
    @22
    @23
    @20
    cB
    c.pl
    cP
    @7
    cF
    @5
    r1pid.b
    r1pid.m
    @14
    grpnpcan
    syl3anc
    3eqtrrd
end
