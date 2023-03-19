include "wcel.mm"
include "wnf.mm"
include "wtru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfeld.mm"
include "trud.mm"

theorem nfel
  param vx: setvar x
  param cA: class A
  param cB: class B
  let vz: setvar z
  let vy: setvar y
  assume nfnfc.1: |- F/_ x A
  assume nfeq.2: |- F/_ x B


  assert |- F/ x A e. B

  proof
    cA
    cB
    wcel
    vx
    wnf
    wtru
    vx
    cA
    cB
    vx
    cA
    wnfc
    wtru
    nfnfc.1
    a1i
    vx
    cB
    wnfc
    wtru
    nfeq.2
    a1i
    nfeld
    trud
end
