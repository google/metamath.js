include "wceq.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "feq123.mm"
include "mp3an.mm"

theorem feq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume feq12i.1: |- F = G
  assume feq12i.2: |- A = B


  assert |- ( F : A --> C <-> G : B --> C )

  proof
    cF
    cG
    wceq
    cA
    cB
    wceq
    cC
    cC
    wceq
    cA
    cC
    cF
    wf
    cB
    cC
    cG
    wf
    wb
    feq12i.1
    feq12i.2
    cC
    eqid
    cA
    cC
    cB
    cC
    cF
    cG
    feq123
    mp3an
end
