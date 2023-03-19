include "csymdif.mm"
include "cdif.mm"
include "cun.mm"
include "df-symdif.mm"
include "nfdif.mm"
include "nfun.mm"
include "nfcxfr.mm"

theorem nfsymdif
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfsymdif.1: |- F/_ x A
  assume nfsymdif.2: |- F/_ x B


  assert |- F/_ x ( A /_\ B )

  proof
    vx
    cA
    cB
    csymdif
    cA
    cB
    cdif
    #
    cB
    cA
    cdif
    #
    cun
    cA
    cB
    df-symdif
    vx
    @0
    @1
    vx
    cA
    cB
    nfsymdif.1
    nfsymdif.2
    nfdif
    vx
    cB
    cA
    nfsymdif.2
    nfsymdif.1
    nfdif
    nfun
    nfcxfr
end
