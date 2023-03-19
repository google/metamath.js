include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "club.mm"
include "catm.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "pmapssat.mm"
include "polval2N.mm"
include "syldan.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "crab.mm"
include "pmapval.mm"
include "fveq2d.mm"
include "coml.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "hlomcmat.mm"
include "atlatmstc.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem polpmapN
  let cB: class B
  let cP: class P
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  assume polpmap.b: |- B = ( Base ` K )
  assume polpmap.o: |- ._|_ = ( oc ` K )
  assume polpmap.m: |- M = ( pmap ` K )
  assume polpmap.p: |- P = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( P ` ( M ` X ) ) = ( M ` ( ._|_ ` X ) ) )

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
    cP
    cfv
    #
    @3
    cK
    club
    cfv
    #
    cfv
    #
    c.pe
    cfv
    #
    cM
    cfv
    #
    cX
    c.pe
    cfv
    #
    cM
    cfv
    @0
    @1
    @3
    cK
    catm
    cfv
    #
    wss
    @4
    @8
    wceq
    @10
    cB
    chlt
    cK
    cM
    cX
    polpmap.b
    @10
    eqid
    #
    polpmap.m
    pmapssat
    @10
    cP
    @5
    cK
    cM
    c.pe
    @3
    @5
    eqid
    #
    polpmap.o
    @11
    polpmap.m
    polpmap.p
    polval2N
    syldan
    @2
    @7
    @9
    cM
    @2
    @6
    cX
    c.pe
    @2
    @6
    vp
    cv
    cX
    cK
    cple
    cfv
    #
    wbr
    vp
    @10
    crab
    #
    @5
    cfv
    #
    cX
    @2
    @3
    @14
    @5
    @10
    cB
    chlt
    cK
    @13
    cM
    cX
    vp
    polpmap.b
    @13
    eqid
    #
    @11
    polpmap.m
    pmapval
    fveq2d
    @0
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    cal
    wcel
    w3a
    @1
    @15
    cX
    wceq
    cK
    hlomcmat
    vp
    @10
    cB
    @5
    cK
    @13
    cX
    polpmap.b
    @16
    @12
    @11
    atlatmstc
    sylan
    eqtrd
    fveq2d
    fveq2d
    eqtrd
end
