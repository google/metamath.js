include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "cdg1.mm"
include "cco1.mm"
include "cui.mm"
include "eqid.mm"
include "isuc1p.mm"
include "simp1bi.mm"

theorem uc1pcl
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cF: class F
  assume uc1pcl.p: |- P = ( Poly1 ` R )
  assume uc1pcl.b: |- B = ( Base ` P )
  assume uc1pcl.c: |- C = ( Unic1p ` R )


  assert |- ( F e. C -> F e. B )

  proof
    cF
    cC
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
    cui
    cfv
    #
    wcel
    cB
    cC
    @1
    cP
    cR
    @2
    cF
    @0
    uc1pcl.p
    uc1pcl.b
    @0
    eqid
    @1
    eqid
    uc1pcl.c
    @2
    eqid
    isuc1p
    simp1bi
end
