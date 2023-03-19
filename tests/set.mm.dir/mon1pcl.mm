include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "cdg1.mm"
include "cco1.mm"
include "cur.mm"
include "wceq.mm"
include "eqid.mm"
include "ismon1p.mm"
include "simp1bi.mm"

theorem mon1pcl
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cM: class M
  assume uc1pcl.p: |- P = ( Poly1 ` R )
  assume uc1pcl.b: |- B = ( Base ` P )
  assume mon1pcl.m: |- M = ( Monic1p ` R )


  assert |- ( F e. M -> F e. B )

  proof
    cF
    cM
    wcel
    cF
    cB
    wcel
    cF
    cP
    c0g
    cfv
    #
    wne
    cF
    cR
    cdg1
    cfv
    #
    cfv
    cF
    cco1
    cfv
    cfv
    cR
    cur
    cfv
    #
    wceq
    cB
    @1
    cP
    cR
    @2
    cF
    cM
    @0
    uc1pcl.p
    uc1pcl.b
    @0
    eqid
    @1
    eqid
    mon1pcl.m
    @2
    eqid
    ismon1p
    simp1bi
end
