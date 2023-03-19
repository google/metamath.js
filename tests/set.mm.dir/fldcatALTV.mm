include "cfield.mm"
include "cv.mm"
include "crg.mm"
include "wcel.mm"
include "cdr.mm"
include "ccrg.mm"
include "wa.mm"
include "isfld.mm"
include "crngring.mm"
include "adantl.mm"
include "sylbi.mm"
include "rgen.mm"
include "sringcatALTV.mm"

theorem fldcatALTV
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume drhmsubcALTV.c: |- C = ( U i^i DivRing )
  assume drhmsubcALTV.j: |- J = ( r e. C , s e. C |-> ( r RingHom s ) )
  assume fldhmsubcALTV.d: |- D = ( U i^i Field )
  assume fldhmsubcALTV.f: |- F = ( r e. D , s e. D |-> ( r RingHom s ) )

  disjoint C r
  disjoint C s
  disjoint r s
  disjoint U r
  disjoint U s
  disjoint V r
  disjoint V s
  disjoint D r
  disjoint D s
  disjoint k x
  assert |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat F ) e. Cat )

  proof
    cD
    cfield
    cU
    cF
    cV
    vs
    vr
    vr
    cv
    #
    crg
    wcel
    #
    vr
    cfield
    @0
    cfield
    wcel
    @0
    cdr
    wcel
    #
    @0
    ccrg
    wcel
    #
    wa
    @1
    @0
    isfld
    @3
    @1
    @2
    @0
    crngring
    adantl
    sylbi
    rgen
    fldhmsubcALTV.d
    fldhmsubcALTV.f
    sringcatALTV
end
