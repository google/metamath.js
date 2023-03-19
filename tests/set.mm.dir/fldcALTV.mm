include "wcel.mm"
include "cringcALTV.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "ccat.mm"
include "cvv.mm"
include "fvexd.mm"
include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "crh.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "cdr.mm"
include "cin.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "cfield.mm"
include "wss.mm"
include "ccrg.mm"
include "df-field.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sslin.mm"
include "mp1i.mm"
include "3sstr4g.mm"
include "rescabs.mm"
include "fldcatALTV.mm"
include "eqeltrd.mm"

theorem fldcALTV
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
  assert |- ( U e. V -> ( ( ( RingCatALTV ` U ) |`cat J ) |`cat F ) e. Cat )

  proof
    cU
    cV
    wcel
    #
    cU
    cringcALTV
    cfv
    #
    cJ
    cresc
    co
    cF
    cresc
    co
    @1
    cF
    cresc
    co
    ccat
    @0
    @1
    cC
    cD
    cJ
    cF
    cvv
    cvv
    @0
    cU
    cringcALTV
    fvexd
    cJ
    cC
    cC
    cxp
    wfn
    @0
    vr
    vs
    cC
    cC
    vr
    cv
    #
    vs
    cv
    #
    crh
    co
    #
    cJ
    drhmsubcALTV.j
    @2
    @3
    crh
    ovex
    #
    fnmpt2i
    a1i
    cF
    cD
    cD
    cxp
    wfn
    @0
    vr
    vs
    cD
    cD
    @4
    cF
    fldhmsubcALTV.f
    @5
    fnmpt2i
    a1i
    @0
    cC
    cU
    cdr
    cin
    #
    cvv
    drhmsubcALTV.c
    cU
    cdr
    cV
    inex1g
    syl5eqel
    @0
    cU
    cfield
    cin
    #
    @6
    cD
    cC
    cfield
    cdr
    wss
    @7
    @6
    wss
    @0
    cfield
    cdr
    ccrg
    cin
    cdr
    df-field
    cdr
    ccrg
    inss1
    eqsstri
    cfield
    cdr
    cU
    sslin
    mp1i
    fldhmsubcALTV.d
    drhmsubcALTV.c
    3sstr4g
    rescabs
    cC
    cD
    cU
    cF
    cJ
    cV
    vs
    vr
    drhmsubcALTV.c
    drhmsubcALTV.j
    fldhmsubcALTV.d
    fldhmsubcALTV.f
    fldcatALTV
    eqeltrd
end
