include "wcel.mm"
include "cringcALTV.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "eqid.mm"
include "srhmsubcALTV.mm"
include "subccat.mm"

theorem sringcatALTV
  let cC: class C
  let cS: class S
  let cU: class U
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume srhmsubcALTV.s: |- A. r e. S r e. Ring
  assume srhmsubcALTV.c: |- C = ( U i^i S )
  assume srhmsubcALTV.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )

  disjoint S r
  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint S x
  disjoint U f
  disjoint U g
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
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
    cS
    cU
    cJ
    cV
    vs
    vr
    srhmsubcALTV.s
    srhmsubcALTV.c
    srhmsubcALTV.j
    srhmsubcALTV
    subccat
end
