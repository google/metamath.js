include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "c0.mm"
include "cin.mm"
include "simpll.mm"
include "simplr.mm"
include "polssatN.mm"
include "adantr.mm"
include "poldmj1N.mm"
include "syl3anc.mm"
include "pnonsingN.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "cpscN.mm"
include "simpr.mm"
include "wb.mm"
include "eqid.mm"
include "ispsubclN.mm"
include "ad2antrr.mm"
include "mpbir2and.mm"
include "polsubclN.mm"
include "2polssN.mm"
include "osumclN.mm"
include "syl31anc.mm"
include "psubcli2N.mm"
include "pol0N.mm"
include "3eqtr3d.mm"

theorem pexmidN
  let cA: class A
  let c.pl: class .+
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume pexmid.a: |- A = ( Atoms ` K )
  assume pexmid.p: |- .+ = ( +P ` K )
  assume pexmid.o: |- ._|_ = ( _|_P ` K )


  assert |- ( ( ( K e. HL /\ X C_ A ) /\ ( ._|_ ` ( ._|_ ` X ) ) = X ) -> ( X .+ ( ._|_ ` X ) ) = A )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    wceq
    #
    wa
    #
    cX
    @3
    c.pl
    co
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    c0
    c.pe
    cfv
    #
    @7
    cA
    @6
    @8
    c0
    c.pe
    @6
    @8
    @3
    @4
    cin
    #
    c0
    @6
    @0
    @1
    @3
    cA
    wss
    #
    @8
    @11
    wceq
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    @2
    @12
    @5
    cA
    cK
    c.pe
    cX
    pexmid.a
    pexmid.o
    polssatN
    adantr
    #
    cA
    c.pl
    cX
    @3
    cK
    c.pe
    pexmid.a
    pexmid.p
    pexmid.o
    poldmj1N
    syl3anc
    @6
    @0
    @12
    @11
    c0
    wceq
    @13
    @15
    cA
    c.pe
    cK
    @3
    pexmid.a
    pexmid.o
    pnonsingN
    syl2anc
    eqtrd
    fveq2d
    @6
    @0
    @7
    cK
    cpscN
    cfv
    #
    wcel
    #
    @9
    @7
    wceq
    @13
    @6
    @0
    cX
    @16
    wcel
    #
    @3
    @16
    wcel
    #
    cX
    @4
    wss
    #
    @17
    @13
    @6
    @18
    @1
    @5
    @14
    @2
    @5
    simpr
    @0
    @18
    @1
    @5
    wa
    wb
    @1
    @5
    cA
    @16
    chlt
    cK
    c.pe
    cX
    pexmid.a
    pexmid.o
    @16
    eqid
    #
    ispsubclN
    ad2antrr
    mpbir2and
    @2
    @19
    @5
    cA
    @16
    cK
    c.pe
    cX
    pexmid.a
    pexmid.o
    @21
    polsubclN
    adantr
    @2
    @20
    @5
    cA
    cK
    c.pe
    cX
    pexmid.a
    pexmid.o
    2polssN
    adantr
    @16
    c.pl
    cK
    c.pe
    cX
    @3
    pexmid.p
    pexmid.o
    @21
    osumclN
    syl31anc
    @16
    chlt
    cK
    c.pe
    @7
    pexmid.o
    @21
    psubcli2N
    syl2anc
    @0
    @10
    cA
    wceq
    @1
    @5
    cA
    chlt
    cK
    c.pe
    pexmid.a
    pexmid.o
    pol0N
    ad2antrr
    3eqtr3d
end
