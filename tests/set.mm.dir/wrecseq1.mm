include "wceq.mm"
include "cwrecs.mm"
include "eqid.mm"
include "wrecseq123.mm"
include "mp3an23.mm"

theorem wrecseq1
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( R = S -> wrecs ( R , A , F ) = wrecs ( S , A , F ) )

  proof
    cR
    cS
    wceq
    cA
    cA
    wceq
    cF
    cF
    wceq
    cA
    cR
    cF
    cwrecs
    cA
    cS
    cF
    cwrecs
    wceq
    cA
    eqid
    cF
    eqid
    cA
    cA
    cR
    cS
    cF
    cF
    wrecseq123
    mp3an23
end
