include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cq1p.mm"
include "cfv.mm"
include "cmulr.mm"
include "csg.mm"
include "wceq.mm"
include "simp2.mm"
include "uc1pcl.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "r1pval.mm"
include "syl2anc.mm"
include "cgrp.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "q1pcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "eqeltrd.mm"

theorem r1pcl
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  assume r1pval.e: |- E = ( rem1p ` R )
  assume r1pval.p: |- P = ( Poly1 ` R )
  assume r1pval.b: |- B = ( Base ` P )
  assume r1pcl.c: |- C = ( Unic1p ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( F E G ) e. B )

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
    cE
    co
    #
    cF
    cF
    cG
    cR
    cq1p
    cfv
    #
    co
    #
    cG
    cP
    cmulr
    cfv
    #
    co
    #
    cP
    csg
    cfv
    #
    co
    #
    cB
    @3
    @1
    cG
    cB
    wcel
    #
    @4
    @10
    wceq
    @0
    @1
    @2
    simp2
    #
    @2
    @0
    @11
    @1
    cB
    cC
    cP
    cR
    cG
    r1pval.p
    r1pval.b
    r1pcl.c
    uc1pcl
    3ad2ant3
    #
    cB
    cP
    @5
    cR
    @7
    cE
    cF
    cG
    @9
    r1pval.e
    r1pval.p
    r1pval.b
    @5
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    r1pval
    syl2anc
    @3
    cP
    cgrp
    wcel
    #
    @1
    @8
    cB
    wcel
    #
    @10
    cB
    wcel
    @3
    cP
    crg
    wcel
    #
    @17
    @0
    @1
    @19
    @2
    cP
    cR
    r1pval.p
    ply1ring
    3ad2ant1
    #
    cP
    ringgrp
    syl
    @12
    @3
    @19
    @6
    cB
    wcel
    @11
    @18
    @20
    cB
    cC
    cP
    @5
    cR
    cF
    cG
    @14
    r1pval.p
    r1pval.b
    r1pcl.c
    q1pcl
    @13
    cB
    cP
    @7
    @6
    cG
    r1pval.b
    @15
    ringcl
    syl3anc
    cB
    cP
    @9
    cF
    @8
    r1pval.b
    @16
    grpsubcl
    syl3anc
    eqeltrd
end
