include "wcel.mm"
include "cringc.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "eqid.mm"
include "crhmsubc.mm"
include "subccat.mm"

theorem cringcat
  let cC: class C
  let cU: class U
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume crhmsubc.c: |- C = ( U i^i CRing )
  assume crhmsubc.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint k x
  assert |- ( U e. V -> ( ( RingCat ` U ) |`cat J ) e. Cat )

  proof
    cU
    cV
    wcel
    cU
    cringc
    cfv
    #
    @0
    cJ
    cresc
    co
    #
    cJ
    @1
    eqid
    cC
    cU
    cJ
    cV
    vs
    vr
    crhmsubc.c
    crhmsubc.j
    crhmsubc
    subccat
end
