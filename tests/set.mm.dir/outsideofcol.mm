include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "ccolin.mm"
include "cbtwn.mm"
include "wn.mm"
include "broutsideof.mm"
include "simplbi.mm"

theorem outsideofcol
  let cP: class P
  let cQ: class Q
  let cR: class R


  assert |- ( P OutsideOf <. Q , R >. -> P Colinear <. Q , R >. )

  proof
    cP
    cQ
    cR
    cop
    #
    coutsideof
    wbr
    cP
    @0
    ccolin
    wbr
    cP
    @0
    cbtwn
    wbr
    wn
    cQ
    cR
    cP
    broutsideof
    simplbi
end
