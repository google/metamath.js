include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "csg.mm"
include "cdg1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "q1peqb.mm"
include "mpbiri.mm"
include "simpld.mm"

theorem q1pcl
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cF: class F
  let cG: class G
  assume q1pcl.q: |- Q = ( quot1p ` R )
  assume q1pcl.p: |- P = ( Poly1 ` R )
  assume q1pcl.b: |- B = ( Base ` P )
  assume q1pcl.c: |- C = ( Unic1p ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. C ) -> ( F Q G ) e. B )

  proof
    cR
    crg
    wcel
    cF
    cB
    wcel
    cG
    cC
    wcel
    w3a
    #
    cF
    cG
    cQ
    co
    #
    cB
    wcel
    #
    cF
    @1
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
    cR
    cdg1
    cfv
    #
    cfv
    cG
    @5
    cfv
    clt
    wbr
    #
    @0
    @2
    @6
    wa
    @1
    @1
    wceq
    @1
    eqid
    cB
    cC
    @5
    cP
    cQ
    cR
    @3
    cF
    cG
    @4
    @1
    q1pcl.q
    q1pcl.p
    q1pcl.b
    @5
    eqid
    @4
    eqid
    @3
    eqid
    q1pcl.c
    q1peqb
    mpbiri
    simpld
end
