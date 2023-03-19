include "c1o.mm"
include "c0.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "1n0.mm"
include "neii.mm"
include "elsni.mm"
include "mto.mm"
include "nelir.mm"

theorem bj-1nel0



  assert |- 1o e/ { (/) }

  proof
    c1o
    c0
    csn
    #
    c1o
    @0
    wcel
    c1o
    c0
    wceq
    c1o
    c0
    1n0
    neii
    c1o
    c0
    elsni
    mto
    nelir
end
