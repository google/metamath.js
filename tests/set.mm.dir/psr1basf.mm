include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "psr1bas.mm"
include "eleq2s.mm"

theorem psr1basf
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let cK: class K
  assume psr1rcl.p: |- P = ( PwSer1 ` R )
  assume psr1rcl.b: |- B = ( Base ` P )
  assume psr1basf.k: |- K = ( Base ` R )


  assert |- ( F e. B -> F : ( NN0 ^m 1o ) --> K )

  proof
    cn0
    c1o
    cmap
    co
    #
    cK
    cF
    wf
    cF
    cK
    @0
    cmap
    co
    cB
    cF
    cK
    @0
    elmapi
    cB
    cR
    cP
    cK
    psr1rcl.p
    psr1rcl.b
    psr1basf.k
    psr1bas
    eleq2s
end
