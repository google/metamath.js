include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "cpolN.mm"
include "wceq.mm"
include "eqid.mm"
include "pmapj2N.mm"
include "adantr.mm"
include "cpscN.mm"
include "simpl1.mm"
include "wss.mm"
include "simpl2.mm"
include "pmapsubclN.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "wb.mm"
include "cops.mm"
include "hlop.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opoccl.mm"
include "pmaple.mm"
include "syld3an3.mm"
include "biimpa.mm"
include "polpmapN.mm"
include "sseqtr4d.mm"
include "osumclN.mm"
include "syl31anc.mm"
include "psubcli2N.mm"
include "eqtrd.mm"

theorem pmapojoinN
  let cB: class B
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume pmapojoin.b: |- B = ( Base ` K )
  assume pmapojoin.l: |- .<_ = ( le ` K )
  assume pmapojoin.j: |- .\/ = ( join ` K )
  assume pmapojoin.m: |- M = ( pmap ` K )
  assume pmapojoin.o: |- ._|_ = ( oc ` K )
  assume pmapojoin.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X .<_ ( ._|_ ` Y ) ) -> ( M ` ( X .\/ Y ) ) = ( ( M ` X ) .+ ( M ` Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.pe
    cfv
    #
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    c.or
    co
    cM
    cfv
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    c.pl
    co
    #
    cK
    cpolN
    cfv
    #
    cfv
    @11
    cfv
    #
    @10
    @3
    @7
    @12
    wceq
    @5
    cB
    c.pl
    c.or
    cK
    cM
    @11
    cX
    cY
    pmapojoin.b
    pmapojoin.j
    pmapojoin.m
    pmapojoin.p
    @11
    eqid
    #
    pmapj2N
    adantr
    @6
    @0
    @10
    cK
    cpscN
    cfv
    #
    wcel
    #
    @12
    @10
    wceq
    @0
    @1
    @2
    @5
    simpl1
    #
    @6
    @0
    @8
    @14
    wcel
    #
    @9
    @14
    wcel
    #
    @8
    @9
    @11
    cfv
    #
    wss
    @15
    @16
    @6
    @0
    @1
    @17
    @16
    @0
    @1
    @2
    @5
    simpl2
    cB
    @14
    cK
    cM
    cX
    pmapojoin.b
    pmapojoin.m
    @14
    eqid
    #
    pmapsubclN
    syl2anc
    @6
    @0
    @2
    @18
    @16
    @0
    @1
    @2
    @5
    simpl3
    #
    cB
    @14
    cK
    cM
    cY
    pmapojoin.b
    pmapojoin.m
    @20
    pmapsubclN
    syl2anc
    @6
    @8
    @4
    cM
    cfv
    #
    @19
    @3
    @5
    @8
    @22
    wss
    #
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @23
    wb
    @3
    cK
    cops
    wcel
    #
    @2
    @24
    @0
    @1
    @25
    @2
    cK
    hlop
    3ad2ant1
    @0
    @1
    @2
    simp3
    cB
    cK
    c.pe
    cY
    pmapojoin.b
    pmapojoin.o
    opoccl
    syl2anc
    cB
    cK
    c.le
    cM
    cX
    @4
    pmapojoin.b
    pmapojoin.l
    pmapojoin.m
    pmaple
    syld3an3
    biimpa
    @6
    @0
    @2
    @19
    @22
    wceq
    @16
    @21
    cB
    @11
    cK
    cM
    c.pe
    cY
    pmapojoin.b
    pmapojoin.o
    pmapojoin.m
    @13
    polpmapN
    syl2anc
    sseqtr4d
    @14
    c.pl
    cK
    @11
    @8
    @9
    pmapojoin.p
    @13
    @20
    osumclN
    syl31anc
    @14
    chlt
    cK
    @11
    @10
    @13
    @20
    psubcli2N
    syl2anc
    eqtrd
end
