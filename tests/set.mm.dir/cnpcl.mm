include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "cnpf.mm"
include "ffvelrnda.mm"

theorem cnpcl
  let cA: class A
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume iscnp2.1: |- X = U. J
  assume iscnp2.2: |- Y = U. K


  assert |- ( ( F e. ( ( J CnP K ) ` P ) /\ A e. X ) -> ( F ` A ) e. Y )

  proof
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cA
    cF
    cP
    cF
    cJ
    cK
    cX
    cY
    iscnp2.1
    iscnp2.2
    cnpf
    ffvelrnda
end
