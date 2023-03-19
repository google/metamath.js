include "wcel.mm"
include "wa.mm"
include "cedring.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "dvhsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cltrn.mm"
include "erngbase.mm"
include "eqtrd.mm"

theorem dvhbase
  let cC: class C
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  assume dvhbase.h: |- H = ( LHyp ` K )
  assume dvhbase.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhbase.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhbase.f: |- F = ( Scalar ` U )
  assume dvhbase.c: |- C = ( Base ` F )


  assert |- ( ( K e. X /\ W e. H ) -> C = E )

  proof
    cK
    cX
    wcel
    cW
    cH
    wcel
    wa
    #
    cC
    cW
    cK
    cedring
    cfv
    cfv
    #
    cbs
    cfv
    #
    cE
    @0
    cC
    cF
    cbs
    cfv
    @2
    dvhbase.c
    @0
    cF
    @1
    cbs
    @1
    cU
    cF
    cH
    cK
    cW
    cX
    dvhbase.h
    @1
    eqid
    #
    dvhbase.u
    dvhbase.f
    dvhsca
    fveq2d
    syl5eq
    @2
    @1
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cE
    cH
    cK
    cX
    cW
    dvhbase.h
    @4
    eqid
    dvhbase.e
    @3
    @2
    eqid
    erngbase
    eqtrd
end
