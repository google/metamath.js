include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cdg1.mm"
include "cco1.mm"
include "cui.mm"
include "eqid.mm"
include "mon1pcl.mm"
include "adantl.mm"
include "mon1pn0.mm"
include "cur.mm"
include "wceq.mm"
include "mon1pldg.mm"
include "1unit.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "isuc1p.mm"
include "syl3anbrc.mm"

theorem mon1puc1p
  let cC: class C
  let cR: class R
  let cM: class M
  let cX: class X
  assume mon1puc1p.c: |- C = ( Unic1p ` R )
  assume mon1puc1p.m: |- M = ( Monic1p ` R )


  assert |- ( ( R e. Ring /\ X e. M ) -> X e. C )

  proof
    cR
    crg
    wcel
    #
    cX
    cM
    wcel
    #
    wa
    #
    cX
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    cX
    @3
    c0g
    cfv
    #
    wne
    #
    cX
    cR
    cdg1
    cfv
    #
    cfv
    cX
    cco1
    cfv
    cfv
    #
    cR
    cui
    cfv
    #
    wcel
    cX
    cC
    wcel
    @1
    @5
    @0
    @4
    @3
    cR
    cX
    cM
    @3
    eqid
    #
    @4
    eqid
    #
    mon1puc1p.m
    mon1pcl
    adantl
    @1
    @7
    @0
    @3
    cR
    cX
    cM
    @6
    @11
    @6
    eqid
    #
    mon1puc1p.m
    mon1pn0
    adantl
    @2
    @9
    cR
    cur
    cfv
    #
    @10
    @1
    @9
    @14
    wceq
    @0
    @8
    cR
    @14
    cX
    cM
    @8
    eqid
    #
    @14
    eqid
    #
    mon1puc1p.m
    mon1pldg
    adantl
    @0
    @14
    @10
    wcel
    @1
    cR
    @10
    @14
    @10
    eqid
    #
    @16
    1unit
    adantr
    eqeltrd
    @4
    cC
    @8
    @3
    cR
    @10
    cX
    @6
    @11
    @12
    @13
    @15
    mon1puc1p.c
    @17
    isuc1p
    syl3anbrc
end
