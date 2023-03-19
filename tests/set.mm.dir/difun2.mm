include "cun.mm"
include "cdif.mm"
include "c0.mm"
include "difundir.mm"
include "difid.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"

theorem difun2
  let cA: class A
  let cB: class B


  assert |- ( ( A u. B ) \ B ) = ( A \ B )

  proof
    cA
    cB
    cun
    cB
    cdif
    cA
    cB
    cdif
    #
    cB
    cB
    cdif
    #
    cun
    @0
    c0
    cun
    @0
    cA
    cB
    cB
    difundir
    @1
    c0
    @0
    cB
    difid
    uneq2i
    @0
    un0
    3eqtri
end
