include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cq1p.mm"
include "cfv.mm"
include "co.mm"
include "cmulr.mm"
include "csg.mm"
include "wceq.mm"
include "wbr.mm"
include "cgrp.mm"
include "wb.mm"
include "ply1ring.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "simp2.mm"
include "eqid.mm"
include "q1pcl.mm"
include "uc1pcl.mm"
include "3ad2ant3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpsubeq0.mm"
include "r1pval.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "dvdsq1p.mm"
include "3bitr4rd.mm"

theorem dvdsr1p
  let cB: class B
  let cC: class C
  let c.pa: class .||
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let c.0: class .0.
  assume dvdsq1p.p: |- P = ( Poly1 ` R )
  assume dvdsq1p.d: |- .|| = ( ||r ` P )
  assume dvdsq1p.b: |- B = ( Base ` P )
  assume dvdsq1p.c: |- C = ( Unic1p ` R )
  assume dvdsr1p.z: |- .0. = ( 0g ` P )
  assume dvdsr1p.e: |- E = ( rem1p ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( G .|| F <-> ( F E G ) = .0. ) )

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
    c.0
    wceq
    #
    cF
    @7
    wceq
    #
    cF
    cG
    cE
    co
    #
    c.0
    wceq
    cG
    cF
    c.pa
    wbr
    @3
    cP
    cgrp
    wcel
    #
    @1
    @7
    cB
    wcel
    #
    @10
    @11
    wb
    @3
    cP
    crg
    wcel
    #
    @13
    @0
    @1
    @15
    @2
    cP
    cR
    dvdsq1p.p
    ply1ring
    3ad2ant1
    #
    cP
    ringgrp
    syl
    @0
    @1
    @2
    simp2
    #
    @3
    @15
    @5
    cB
    wcel
    cG
    cB
    wcel
    #
    @14
    @16
    cB
    cC
    cP
    @4
    cR
    cF
    cG
    @4
    eqid
    #
    dvdsq1p.p
    dvdsq1p.b
    dvdsq1p.c
    q1pcl
    @2
    @0
    @18
    @1
    cB
    cC
    cP
    cR
    cG
    dvdsq1p.p
    dvdsq1p.b
    dvdsq1p.c
    uc1pcl
    3ad2ant3
    #
    cB
    cP
    @6
    @5
    cG
    dvdsq1p.b
    @6
    eqid
    #
    ringcl
    syl3anc
    cB
    cP
    @8
    cF
    @7
    c.0
    dvdsq1p.b
    dvdsr1p.z
    @8
    eqid
    #
    grpsubeq0
    syl3anc
    @3
    @12
    @9
    c.0
    @3
    @1
    @18
    @12
    @9
    wceq
    @17
    @20
    cB
    cP
    @4
    cR
    @6
    cE
    cF
    cG
    @8
    dvdsr1p.e
    dvdsq1p.p
    dvdsq1p.b
    @19
    @21
    @22
    r1pval
    syl2anc
    eqeq1d
    cB
    cC
    c.pa
    cP
    @4
    cR
    @6
    cF
    cG
    dvdsq1p.p
    dvdsq1p.d
    dvdsq1p.b
    dvdsq1p.c
    @21
    @19
    dvdsq1p
    3bitr4rd
end
