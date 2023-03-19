include "csymdif.mm"
include "cdif.mm"
include "cun.mm"
include "c0.mm"
include "df-symdif.mm"
include "difid.mm"
include "uneq12i.mm"
include "un0.mm"
include "3eqtri.mm"

theorem symdifid
  let cA: class A


  assert |- ( A /_\ A ) = (/)

  proof
    cA
    cA
    csymdif
    cA
    cA
    cdif
    #
    @0
    cun
    c0
    c0
    cun
    c0
    cA
    cA
    df-symdif
    @0
    c0
    @0
    c0
    cA
    difid
    #
    @1
    uneq12i
    c0
    un0
    3eqtri
end
