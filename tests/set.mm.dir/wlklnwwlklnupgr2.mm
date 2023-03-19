include "cupgr.mm"
include "wcel.mm"
include "wlkiswwlksupgr2.mm"
include "wlklnwwlkln2lem.mm"

theorem wlklnwwlklnupgr2
  let cP: class P
  let vf: setvar f
  let cG: class G
  let cN: class N

  disjoint G f
  disjoint N f
  disjoint P f
  assert |- ( G e. UPGraph -> ( P e. ( N WWalksN G ) -> E. f ( f ( Walks ` G ) P /\ ( # ` f ) = N ) ) )

  proof
    cG
    cupgr
    wcel
    cP
    vf
    cG
    cN
    cP
    vf
    cG
    wlkiswwlksupgr2
    wlklnwwlkln2lem
end
