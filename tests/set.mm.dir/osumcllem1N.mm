include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "csn.mm"
include "co.mm"
include "sspadd1.mm"
include "adantr.mm"
include "cfv.mm"
include "simpl1.mm"
include "paddssat.mm"
include "2polssN.mm"
include "syl2anc.mm"
include "syl6sseqr.mm"
include "sstrd.mm"
include "simpr.mm"
include "snssd.mm"
include "cpsubsp.mm"
include "wb.mm"
include "simpl2.mm"
include "polssatN.mm"
include "syl5eqss.mm"
include "eqid.mm"
include "polsubN.mm"
include "syl5eqel.mm"
include "paddss.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "sseqin2.mm"
include "sylib.mm"

theorem osumcllem1N
  let cA: class A
  let cC: class C
  let c.pl: class .+
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ p e. U ) -> ( U i^i M ) = M )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    vp
    cv
    #
    cU
    wcel
    #
    wa
    #
    cM
    cU
    wss
    cU
    cM
    cin
    cM
    wceq
    @6
    cM
    cX
    @4
    csn
    #
    c.pl
    co
    #
    cU
    osumcllem.m
    @6
    cX
    cU
    wss
    #
    @7
    cU
    wss
    #
    @8
    cU
    wss
    #
    @6
    cX
    cX
    cY
    c.pl
    co
    #
    cU
    @3
    cX
    @12
    wss
    @5
    cA
    chlt
    c.pl
    cK
    cX
    cY
    osumcllem.a
    osumcllem.p
    sspadd1
    adantr
    @6
    @12
    @12
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cU
    @6
    @0
    @12
    cA
    wss
    #
    @12
    @14
    wss
    @0
    @1
    @2
    @5
    simpl1
    #
    @3
    @15
    @5
    cA
    chlt
    c.pl
    cK
    cX
    cY
    osumcllem.a
    osumcllem.p
    paddssat
    adantr
    #
    cA
    cK
    c.pe
    @12
    osumcllem.a
    osumcllem.o
    2polssN
    syl2anc
    osumcllem.u
    syl6sseqr
    sstrd
    @6
    @4
    cU
    @3
    @5
    simpr
    snssd
    #
    @6
    @0
    @1
    @7
    cA
    wss
    cU
    cK
    cpsubsp
    cfv
    #
    wcel
    @9
    @10
    wa
    @11
    wb
    @16
    @0
    @1
    @2
    @5
    simpl2
    @6
    @7
    cU
    cA
    @18
    @6
    cU
    @14
    cA
    osumcllem.u
    @6
    @0
    @13
    cA
    wss
    #
    @14
    cA
    wss
    @16
    @6
    @0
    @15
    @20
    @16
    @17
    cA
    cK
    c.pe
    @12
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    #
    cA
    cK
    c.pe
    @13
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    syl5eqss
    sstrd
    @6
    cU
    @14
    @19
    osumcllem.u
    @6
    @0
    @20
    @14
    @19
    wcel
    @16
    @21
    cA
    @19
    cK
    c.pe
    @13
    osumcllem.a
    @19
    eqid
    #
    osumcllem.o
    polsubN
    syl2anc
    syl5eqel
    cA
    chlt
    c.pl
    @19
    cK
    cX
    @7
    cU
    osumcllem.a
    @22
    osumcllem.p
    paddss
    syl13anc
    mpbi2and
    syl5eqss
    cM
    cU
    sseqin2
    sylib
end
