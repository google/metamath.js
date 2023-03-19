include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "coc.mm"
include "eqid.mm"
include "polpmapN.mm"
include "fveq2d.mm"
include "wceq.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "sylan.mm"
include "syldan.mm"
include "opococ.mm"
include "3eqtrd.mm"

theorem 2polpmapN
  let cB: class B
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  assume 2polpmap.b: |- B = ( Base ` K )
  assume 2polpmap.m: |- M = ( pmap ` K )
  assume 2polpmap.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( ._|_ ` ( ._|_ ` ( M ` X ) ) ) = ( M ` X ) )

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
    #
    cX
    cM
    cfv
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cM
    cfv
    #
    c.pe
    cfv
    #
    @6
    @5
    cfv
    #
    cM
    cfv
    #
    @3
    @2
    @4
    @7
    c.pe
    cB
    c.pe
    cK
    cM
    @5
    cX
    2polpmap.b
    @5
    eqid
    #
    2polpmap.m
    2polpmap.p
    polpmapN
    fveq2d
    @0
    @1
    @6
    cB
    wcel
    #
    @8
    @10
    wceq
    @0
    cK
    cops
    wcel
    #
    @1
    @12
    cK
    hlop
    #
    cB
    cK
    @5
    cX
    2polpmap.b
    @11
    opoccl
    sylan
    cB
    c.pe
    cK
    cM
    @5
    @6
    2polpmap.b
    @11
    2polpmap.m
    2polpmap.p
    polpmapN
    syldan
    @2
    @9
    cX
    cM
    @0
    @13
    @1
    @9
    cX
    wceq
    @14
    cB
    cK
    @5
    cX
    2polpmap.b
    @11
    opococ
    sylan
    fveq2d
    3eqtrd
end
