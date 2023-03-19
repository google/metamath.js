include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "csn.mm"
include "co.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "snssd.mm"
include "cfv.mm"
include "paddssat.mm"
include "adantr.mm"
include "polssatN.mm"
include "syl2anc.mm"
include "syl5eqss.mm"
include "sstrd.mm"
include "sspadd1.mm"
include "syl3anc.mm"
include "syl6sseqr.mm"
include "osumcllem1N.mm"
include "sseqtr4d.mm"

theorem osumcllem2N
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


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ p e. U ) -> X C_ ( U i^i M ) )

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
    cX
    cM
    cU
    cM
    cin
    @6
    cX
    cX
    @4
    csn
    #
    c.pl
    co
    #
    cM
    @6
    @0
    @1
    @7
    cA
    wss
    cX
    @8
    wss
    @0
    @1
    @2
    @5
    simpl1
    #
    @0
    @1
    @2
    @5
    simpl2
    @6
    @7
    cU
    cA
    @6
    @4
    cU
    @3
    @5
    simpr
    snssd
    @6
    cU
    cX
    cY
    c.pl
    co
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cA
    osumcllem.u
    @6
    @0
    @11
    cA
    wss
    #
    @12
    cA
    wss
    @9
    @6
    @0
    @10
    cA
    wss
    #
    @13
    @9
    @3
    @14
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
    cA
    cK
    c.pe
    @10
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    cA
    cK
    c.pe
    @11
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    syl5eqss
    sstrd
    cA
    chlt
    c.pl
    cK
    cX
    @7
    osumcllem.a
    osumcllem.p
    sspadd1
    syl3anc
    osumcllem.m
    syl6sseqr
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem1N
    sseqtr4d
end
