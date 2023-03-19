include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "catm.mm"
include "wss.mm"
include "cpolN.mm"
include "wceq.mm"
include "eqid.mm"
include "pmapssat.mm"
include "2polpmapN.mm"
include "wb.mm"
include "ispsubclN.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem pmapsubclN
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cX: class X
  assume pmapsubcl.b: |- B = ( Base ` K )
  assume pmapsubcl.m: |- M = ( pmap ` K )
  assume pmapsubcl.c: |- C = ( PSubCl ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( M ` X ) e. C )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    cM
    cfv
    #
    cC
    wcel
    #
    @2
    cK
    catm
    cfv
    #
    wss
    #
    @2
    cK
    cpolN
    cfv
    #
    cfv
    @6
    cfv
    @2
    wceq
    #
    @4
    cB
    chlt
    cK
    cM
    cX
    pmapsubcl.b
    @4
    eqid
    #
    pmapsubcl.m
    pmapssat
    cB
    cK
    cM
    @6
    cX
    pmapsubcl.b
    pmapsubcl.m
    @6
    eqid
    #
    2polpmapN
    @0
    @3
    @5
    @7
    wa
    wb
    @1
    @4
    cC
    chlt
    cK
    @6
    @2
    @8
    @9
    pmapsubcl.c
    ispsubclN
    adantr
    mpbir2and
end
