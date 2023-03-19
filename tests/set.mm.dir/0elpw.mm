include "c0.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "0ss.mm"
include "0ex.mm"
include "elpw.mm"
include "mpbir.mm"

theorem 0elpw
  let cA: class A


  assert |- (/) e. ~P A

  proof
    c0
    cA
    cpw
    wcel
    c0
    cA
    wss
    cA
    0ss
    c0
    cA
    0ex
    elpw
    mpbir
end
