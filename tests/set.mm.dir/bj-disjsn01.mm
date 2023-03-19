include "c0.mm"
include "c1o.mm"
include "wne.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "ax-mp.mm"

theorem bj-disjsn01



  assert |- ( { (/) } i^i { 1o } ) = (/)

  proof
    c0
    c1o
    wne
    c0
    csn
    c1o
    csn
    cin
    c0
    wceq
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    disjsn2
    ax-mp
end
