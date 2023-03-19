include "cuspgr.mm"
include "wcel.mm"
include "wlkiswwlks2.mm"
include "wlklnwwlkln2lem.mm"

theorem wlklnwwlkln2
  let cP: class P
  let vf: setvar f
  let cG: class G
  let cN: class N

  disjoint G f
  disjoint N f
  disjoint P f
  assert |- ( G e. USPGraph -> ( P e. ( N WWalksN G ) -> E. f ( f ( Walks ` G ) P /\ ( # ` f ) = N ) ) )

  proof
    cG
    cuspgr
    wcel
    cP
    vf
    cG
    cN
    cP
    vf
    cG
    wlkiswwlks2
    wlklnwwlkln2lem
end
