include "wceq.mm"
include "cwrecs.mm"
include "eqid.mm"
include "wrecseq123.mm"
include "mp3an12.mm"

theorem wrecseq3
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G


  assert |- ( F = G -> wrecs ( R , A , F ) = wrecs ( R , A , G ) )

  proof
    cR
    cR
    wceq
    cA
    cA
    wceq
    cF
    cG
    wceq
    cA
    cR
    cF
    cwrecs
    cA
    cR
    cG
    cwrecs
    wceq
    cR
    eqid
    cA
    eqid
    cA
    cA
    cR
    cR
    cF
    cG
    wrecseq123
    mp3an12
end
