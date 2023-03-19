include "wceq.mm"
include "cwrecs.mm"
include "eqid.mm"
include "wrecseq123.mm"
include "mp3an13.mm"

theorem wrecseq2
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F


  assert |- ( A = B -> wrecs ( R , A , F ) = wrecs ( R , B , F ) )

  proof
    cR
    cR
    wceq
    cA
    cB
    wceq
    cF
    cF
    wceq
    cA
    cR
    cF
    cwrecs
    cB
    cR
    cF
    cwrecs
    wceq
    cR
    eqid
    cF
    eqid
    cA
    cB
    cR
    cR
    cF
    cF
    wrecseq123
    mp3an13
end
