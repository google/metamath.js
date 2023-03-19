include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cin.mm"
include "incom.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "psubclssatN.mm"
include "3adant3.mm"
include "polssatN.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "poldmj1N.mm"
include "syl3anc.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "ineq1d.mm"
include "polcon2N.mm"
include "syld3an2.mm"
include "poml5N.mm"
include "psubcli2N.mm"
include "3eqtrd.mm"

theorem osumcllem3N
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


  assert |- ( ( K e. HL /\ Y e. C /\ X C_ ( ._|_ ` Y ) ) -> ( ( ._|_ ` X ) i^i U ) = Y )

  proof
    cK
    chlt
    wcel
    #
    cY
    cC
    wcel
    #
    cX
    cY
    c.pe
    cfv
    #
    wss
    #
    w3a
    #
    cX
    c.pe
    cfv
    #
    cU
    cin
    cU
    @5
    cin
    #
    cY
    @5
    cU
    incom
    @4
    @6
    @2
    @5
    cin
    #
    c.pe
    cfv
    #
    @5
    cin
    #
    @2
    c.pe
    cfv
    #
    cY
    @4
    cU
    @8
    @5
    @4
    cU
    cX
    cY
    c.pl
    co
    c.pe
    cfv
    #
    c.pe
    cfv
    @8
    osumcllem.u
    @4
    @11
    @7
    c.pe
    @4
    @11
    @5
    @2
    cin
    #
    @7
    @4
    @0
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    @11
    @12
    wceq
    @0
    @1
    @3
    simp1
    #
    @4
    cX
    @2
    cA
    @0
    @1
    @3
    simp3
    @4
    @0
    @14
    @2
    cA
    wss
    @15
    @0
    @1
    @14
    @3
    cA
    cC
    chlt
    cK
    cY
    osumcllem.a
    osumcllem.c
    psubclssatN
    3adant3
    #
    cA
    cK
    c.pe
    cY
    osumcllem.a
    osumcllem.o
    polssatN
    syl2anc
    sstrd
    #
    @16
    cA
    c.pl
    cX
    cY
    cK
    c.pe
    osumcllem.a
    osumcllem.p
    osumcllem.o
    poldmj1N
    syl3anc
    @5
    @2
    incom
    syl6eq
    fveq2d
    syl5eq
    ineq1d
    @4
    @0
    @13
    cY
    @5
    wss
    #
    @9
    @10
    wceq
    @15
    @17
    @0
    @14
    @1
    @3
    @18
    @16
    cA
    cK
    c.pe
    cX
    cY
    osumcllem.a
    osumcllem.o
    polcon2N
    syld3an2
    cA
    cK
    c.pe
    cY
    cX
    osumcllem.a
    osumcllem.o
    poml5N
    syl3anc
    @0
    @1
    @10
    cY
    wceq
    @3
    cC
    chlt
    cK
    c.pe
    cY
    osumcllem.o
    osumcllem.c
    psubcli2N
    3adant3
    3eqtrd
    syl5eq
end
