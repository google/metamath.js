include "nfcv.mm"
include "reuccats1.mm"

theorem reuccats1v
  let vx: setvar x
  let vv: setvar v
  let cV: class V
  let cW: class W
  let cX: class X

  disjoint V v
  disjoint V x
  disjoint v x
  disjoint W v
  disjoint W x
  disjoint X v
  disjoint X x
  assert |- ( ( W e. Word V /\ A. x e. X ( x e. Word V /\ ( # ` x ) = ( ( # ` W ) + 1 ) ) ) -> ( E! v e. V ( W ++ <" v "> ) e. X -> E! x e. X W = ( x substr <. 0 , ( # ` W ) >. ) ) )

  proof
    vx
    vv
    cV
    cW
    cX
    vv
    cX
    nfcv
    reuccats1
end
