include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cpolN.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "psubcliN.mm"
include "simpld.mm"

theorem psubclssatN
  let cA: class A
  let cC: class C
  let cD: class D
  let cK: class K
  let cX: class X
  assume psubclssat.a: |- A = ( Atoms ` K )
  assume psubclssat.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. D /\ X e. C ) -> X C_ A )

  proof
    cK
    cD
    wcel
    cX
    cC
    wcel
    wa
    cX
    cA
    wss
    cX
    cK
    cpolN
    cfv
    #
    cfv
    @0
    cfv
    cX
    wceq
    cA
    cC
    cD
    cK
    @0
    cX
    psubclssat.a
    @0
    eqid
    psubclssat.c
    psubcliN
    simpld
end
