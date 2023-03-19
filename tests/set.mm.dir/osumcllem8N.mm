include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wn.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "n0.mm"
include "osumcllem7N.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "necon1bd.mm"
include "3impia.mm"

theorem osumcllem8N
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
  let vq: setvar q
  let vr: setvar r
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ ( X C_ ( ._|_ ` Y ) /\ X =/= (/) /\ p e. A ) /\ -. p e. ( X .+ Y ) ) -> ( Y i^i M ) = (/) )

  proof
    cK
    chlt
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    #
    cX
    cY
    c.pe
    cfv
    wss
    cX
    c0
    wne
    vp
    cv
    #
    cA
    wcel
    w3a
    #
    @1
    cX
    cY
    c.pl
    co
    wcel
    #
    wn
    cY
    cM
    cin
    #
    c0
    wceq
    @0
    @2
    wa
    #
    @3
    @4
    c0
    @4
    c0
    wne
    vq
    cv
    @4
    wcel
    #
    vq
    wex
    @5
    @3
    vq
    @4
    n0
    @5
    @6
    @3
    vq
    @0
    @2
    @6
    @3
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
    vq
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem7N
    3expia
    exlimdv
    syl5bi
    necon1bd
    3impia
end
