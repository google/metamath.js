include "wcel.mm"
include "cringcALTV.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "eqid.mm"
include "crhmsubcALTV.mm"
include "subccat.mm"

theorem cringcatALTV
  let cC: class C
  let cU: class U
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume crhmsubcALTV.c: |- C = ( U i^i CRing )
  assume crhmsubcALTV.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint k x
  assert |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat J ) e. Cat )

  proof
    cU
    cV
    wcel
    cU
    cringcALTV
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
    crhmsubcALTV.c
    crhmsubcALTV.j
    crhmsubcALTV
    subccat
end
