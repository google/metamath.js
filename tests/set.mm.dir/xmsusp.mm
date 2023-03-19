include "c0.mm"
include "wne.mm"
include "cxme.mm"
include "wcel.mm"
include "cmetu.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cust.mm"
include "ctopn.mm"
include "cutop.mm"
include "cusp.mm"
include "simp3.mm"
include "cxmt.mm"
include "simp1.mm"
include "xmsxmet.mm"
include "3ad2ant2.mm"
include "cpsmet.mm"
include "xmetpsmet.mm"
include "metuust.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "cmopn.mm"
include "xmetutop.mm"
include "fveq2d.mm"
include "eqid.mm"
include "xmstopn.mm"
include "3eqtr4rd.mm"
include "isusp.mm"
include "sylanbrc.mm"

theorem xmsusp
  let cD: class D
  let cU: class U
  let cF: class F
  let cX: class X
  assume xmsusp.x: |- X = ( Base ` F )
  assume xmsusp.d: |- D = ( ( dist ` F ) |` ( X X. X ) )
  assume xmsusp.u: |- U = ( UnifSt ` F )


  assert |- ( ( X =/= (/) /\ F e. *MetSp /\ U = ( metUnif ` D ) ) -> F e. UnifSp )

  proof
    cX
    c0
    wne
    #
    cF
    cxme
    wcel
    #
    cU
    cD
    cmetu
    cfv
    #
    wceq
    #
    w3a
    #
    cU
    cX
    cust
    cfv
    #
    wcel
    cF
    ctopn
    cfv
    #
    cU
    cutop
    cfv
    #
    wceq
    cF
    cusp
    wcel
    @4
    cU
    @2
    @5
    @0
    @1
    @3
    simp3
    #
    @4
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @2
    @5
    wcel
    #
    @0
    @1
    @3
    simp1
    #
    @1
    @0
    @9
    @3
    cD
    cF
    cX
    xmsusp.x
    xmsusp.d
    xmsxmet
    3ad2ant2
    #
    @9
    @0
    cD
    cX
    cpsmet
    cfv
    wcel
    @10
    cD
    cX
    xmetpsmet
    cD
    cX
    metuust
    sylan2
    syl2anc
    eqeltrd
    @4
    @2
    cutop
    cfv
    #
    cD
    cmopn
    cfv
    #
    @7
    @6
    @4
    @0
    @9
    @13
    @14
    wceq
    @11
    @12
    cD
    cX
    xmetutop
    syl2anc
    @4
    cU
    @2
    cutop
    @8
    fveq2d
    @1
    @0
    @6
    @14
    wceq
    @3
    cD
    @6
    cF
    cX
    @6
    eqid
    #
    xmsusp.x
    xmsusp.d
    xmstopn
    3ad2ant2
    3eqtr4rd
    cX
    cU
    @6
    cF
    xmsusp.x
    xmsusp.u
    @15
    isusp
    sylanbrc
end
