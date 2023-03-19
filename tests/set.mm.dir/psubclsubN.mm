include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cpolN.mm"
include "cfv.mm"
include "eqid.mm"
include "psubcli2N.mm"
include "catm.mm"
include "wss.mm"
include "wceq.mm"
include "psubcliN.mm"
include "simpld.mm"
include "polsubN.mm"
include "syldan.mm"
include "psubssat.mm"
include "eqeltrrd.mm"

theorem psubclsubN
  let cC: class C
  let cS: class S
  let cK: class K
  let cX: class X
  assume psubclsub.s: |- S = ( PSubSp ` K )
  assume psubclsub.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. C ) -> X e. S )

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
    #
    cX
    cK
    cpolN
    cfv
    #
    cfv
    #
    @3
    cfv
    #
    cX
    cS
    cC
    chlt
    cK
    @3
    cX
    @3
    eqid
    #
    psubclsub.c
    psubcli2N
    @0
    @1
    @4
    cK
    catm
    cfv
    #
    wss
    #
    @5
    cS
    wcel
    @0
    @1
    @4
    cS
    wcel
    #
    @8
    @0
    @1
    cX
    @7
    wss
    #
    @9
    @2
    @10
    @5
    cX
    wceq
    @7
    cC
    chlt
    cK
    @3
    cX
    @7
    eqid
    #
    @6
    psubclsub.c
    psubcliN
    simpld
    @7
    cS
    cK
    @3
    cX
    @11
    psubclsub.s
    @6
    polsubN
    syldan
    @7
    chlt
    cS
    cK
    @4
    @11
    psubclsub.s
    psubssat
    syldan
    @7
    cS
    cK
    @3
    @4
    @11
    psubclsub.s
    @6
    polsubN
    syldan
    eqeltrrd
end
