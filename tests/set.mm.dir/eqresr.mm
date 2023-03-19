include "c0r.mm"
include "cop.mm"
include "wceq.mm"
include "eqid.mm"
include "cnr.mm"
include "0r.mm"
include "elexi.mm"
include "opth.mm"
include "mpbiran2.mm"

theorem eqresr
  let cA: class A
  let cB: class B
  assume eqresr.1: |- A e. _V


  assert |- ( <. A , 0R >. = <. B , 0R >. <-> A = B )

  proof
    cA
    c0r
    cop
    cB
    c0r
    cop
    wceq
    cA
    cB
    wceq
    c0r
    c0r
    wceq
    c0r
    eqid
    cA
    c0r
    cB
    c0r
    eqresr.1
    c0r
    cnr
    0r
    elexi
    opth
    mpbiran2
end
