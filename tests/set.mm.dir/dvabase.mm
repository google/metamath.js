include "wcel.mm"
include "wa.mm"
include "cedring.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "dvasca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cltrn.mm"
include "erngbase.mm"
include "eqtrd.mm"

theorem dvabase
  let cC: class C
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  assume dvabase.h: |- H = ( LHyp ` K )
  assume dvabase.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvabase.u: |- U = ( ( DVecA ` K ) ` W )
  assume dvabase.f: |- F = ( Scalar ` U )
  assume dvabase.c: |- C = ( Base ` F )


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
    dvabase.c
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
    dvabase.h
    @1
    eqid
    #
    dvabase.u
    dvabase.f
    dvasca
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
    dvabase.h
    @4
    eqid
    dvabase.e
    @3
    @2
    eqid
    erngbase
    eqtrd
end
