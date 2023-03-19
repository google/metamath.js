include "c0.mm"
include "csymdif.mm"
include "cdif.mm"
include "cun.mm"
include "df-symdif.mm"
include "dif0.mm"
include "0dif.mm"
include "uneq12i.mm"
include "un0.mm"
include "3eqtri.mm"

theorem symdif0
  let cA: class A


  assert |- ( A /_\ (/) ) = A

  proof
    cA
    c0
    csymdif
    cA
    c0
    cdif
    #
    c0
    cA
    cdif
    #
    cun
    cA
    c0
    cun
    cA
    cA
    c0
    df-symdif
    @0
    cA
    @1
    c0
    cA
    dif0
    cA
    0dif
    uneq12i
    cA
    un0
    3eqtri
end
