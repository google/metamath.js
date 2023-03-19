include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "claut.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "idlaut.mm"
include "adantr.mm"
include "fvresi.mm"
include "a1d.mm"
include "rgen.mm"
include "a1i.mm"
include "isldil.mm"
include "mpbir2and.mm"

theorem idldil
  let cA: class A
  let cB: class B
  let cD: class D
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume idldil.b: |- B = ( Base ` K )
  assume idldil.h: |- H = ( LHyp ` K )
  assume idldil.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( K e. A /\ W e. H ) -> ( _I |` B ) e. D )

  proof
    cK
    cA
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cid
    cB
    cres
    #
    cD
    wcel
    @3
    cK
    claut
    cfv
    #
    wcel
    #
    vx
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @6
    @3
    cfv
    @6
    wceq
    #
    wi
    #
    vx
    cB
    wral
    #
    @0
    @5
    @1
    cA
    cB
    @4
    cK
    idldil.b
    @4
    eqid
    #
    idlaut
    adantr
    @11
    @2
    @10
    vx
    cB
    @6
    cB
    wcel
    @9
    @8
    cB
    @6
    fvresi
    a1d
    rgen
    a1i
    vx
    cB
    cA
    cD
    @3
    cH
    @4
    cK
    @7
    cW
    idldil.b
    @7
    eqid
    idldil.h
    @12
    idldil.d
    isldil
    mpbir2and
end
