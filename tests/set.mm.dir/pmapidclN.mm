include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cpolN.mm"
include "cfv.mm"
include "catm.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "psubclssatN.mm"
include "2polvalN.mm"
include "syldan.mm"
include "psubcli2N.mm"
include "eqtr3d.mm"

theorem pmapidclN
  let cC: class C
  let cU: class U
  let cK: class K
  let cM: class M
  let cX: class X
  assume pmapidcl.u: |- U = ( lub ` K )
  assume pmapidcl.m: |- M = ( pmap ` K )
  assume pmapidcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. C ) -> ( M ` ( U ` X ) ) = X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cC
    wcel
    #
    wa
    cX
    cK
    cpolN
    cfv
    #
    cfv
    @2
    cfv
    #
    cX
    cU
    cfv
    cM
    cfv
    #
    cX
    @0
    @1
    cX
    cK
    catm
    cfv
    #
    wss
    @3
    @4
    wceq
    @5
    cC
    chlt
    cK
    cX
    @5
    eqid
    #
    pmapidcl.c
    psubclssatN
    @5
    cU
    cK
    cM
    @2
    cX
    pmapidcl.u
    @6
    pmapidcl.m
    @2
    eqid
    #
    2polvalN
    syldan
    cC
    chlt
    cK
    @2
    cX
    @7
    pmapidcl.c
    psubcli2N
    eqtr3d
end
