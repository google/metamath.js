include "c0.mm"
include "c1o.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "1n0.mm"
include "nesymi.mm"
include "0ex.mm"
include "elsn.mm"
include "mtbir.mm"
include "nelir.mm"

theorem bj-0nel1



  assert |- (/) e/ { 1o }

  proof
    c0
    c1o
    csn
    #
    c0
    @0
    wcel
    c0
    c1o
    wceq
    c1o
    c0
    1n0
    nesymi
    c0
    c1o
    0ex
    elsn
    mtbir
    nelir
end
