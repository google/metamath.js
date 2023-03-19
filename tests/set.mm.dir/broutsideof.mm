include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "ccolin.mm"
include "cbtwn.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "df-outsideof.mm"
include "breqi.mm"
include "brdif.mm"
include "bitri.mm"

theorem broutsideof
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( P OutsideOf <. A , B >. <-> ( P Colinear <. A , B >. /\ -. P Btwn <. A , B >. ) )

  proof
    cP
    cA
    cB
    cop
    #
    coutsideof
    wbr
    cP
    @0
    ccolin
    cbtwn
    cdif
    #
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
    wa
    cP
    @0
    coutsideof
    @1
    df-outsideof
    breqi
    cP
    @0
    ccolin
    cbtwn
    brdif
    bitri
end
