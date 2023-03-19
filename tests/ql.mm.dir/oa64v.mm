include "wf.mm"
include "wt.mm"
include "wn.mm"
include "le0.mm"
include "ax-oa6.mm"
include "id.mm"
include "oa6v4v.mm"

theorem oa64v
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume oa64v.1: |- a =< b '
  assume oa64v.2: |- c =< d '


  assert |- ( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v ( ( a v c ) ^ ( b v d ) ) ) ) )

  proof
    wva
    wvb
    wvc
    wvd
    wf
    wt
    wva
    wvb
    wvc
    wvd
    wf
    wt
    oa64v.1
    oa64v.2
    wt
    wn
    le0
    ax-oa6
    wf
    id
    wt
    id
    oa6v4v
end
