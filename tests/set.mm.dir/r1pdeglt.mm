include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cq1p.mm"
include "cmulr.mm"
include "csg.mm"
include "clt.mm"
include "wceq.mm"
include "simp2.mm"
include "uc1pcl.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "r1pval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "wbr.mm"
include "wa.mm"
include "q1peqb.mm"
include "mpbiri.mm"
include "simprd.mm"
include "eqbrtrd.mm"

theorem r1pdeglt
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  assume r1pval.e: |- E = ( rem1p ` R )
  assume r1pval.p: |- P = ( Poly1 ` R )
  assume r1pval.b: |- B = ( Base ` P )
  assume r1pcl.c: |- C = ( Unic1p ` R )
  assume r1pdeglt.d: |- D = ( deg1 ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( D ` ( F E G ) ) < ( D ` G ) )

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
    cD
    cfv
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
    cP
    csg
    cfv
    #
    co
    #
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    clt
    @3
    @4
    @9
    cD
    @3
    @1
    cG
    cB
    wcel
    #
    @4
    @9
    wceq
    @0
    @1
    @2
    simp2
    @2
    @0
    @12
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
    cB
    cP
    @5
    cR
    @7
    cE
    cF
    cG
    @8
    r1pval.e
    r1pval.p
    r1pval.b
    @5
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    r1pval
    syl2anc
    fveq2d
    @3
    @6
    cB
    wcel
    #
    @10
    @11
    clt
    wbr
    #
    @3
    @16
    @17
    wa
    @6
    @6
    wceq
    @6
    eqid
    cB
    cC
    cD
    cP
    @5
    cR
    @7
    cF
    cG
    @8
    @6
    @13
    r1pval.p
    r1pval.b
    r1pdeglt.d
    @15
    @14
    r1pcl.c
    q1peqb
    mpbiri
    simprd
    eqbrtrd
end
