include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "wn.mm"
include "wne.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "incom.mm"
include "sslin.mm"
include "3ad2ant3.mm"
include "syl5eqss.mm"
include "pnonsingN.mm"
include "3adant3.mm"
include "sseqtrd.mm"
include "ss0b.mm"
include "sylib.mm"
include "adantr.mm"
include "nsyl3.mm"
include "simprr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "simprl.mm"
include "jctild.mm"
include "elin.mm"
include "syl6ibr.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem osumcllem4N
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
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ Y C_ A /\ X C_ ( ._|_ ` Y ) ) /\ ( r e. X /\ q e. Y ) ) -> q =/= r )

  proof
    cK
    chlt
    wcel
    #
    cY
    cA
    wss
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
    vr
    cv
    #
    cX
    wcel
    #
    vq
    cv
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @5
    cX
    cY
    cin
    #
    wcel
    #
    wn
    @7
    @5
    wne
    @12
    @11
    c0
    wceq
    #
    @10
    @11
    @5
    n0i
    @4
    @13
    @9
    @4
    @11
    c0
    wss
    @13
    @4
    @11
    cY
    @2
    cin
    #
    c0
    @4
    @11
    cY
    cX
    cin
    #
    @14
    cX
    cY
    incom
    @3
    @0
    @15
    @14
    wss
    @1
    cX
    @2
    cY
    sslin
    3ad2ant3
    syl5eqss
    @0
    @1
    @14
    c0
    wceq
    @3
    cA
    c.pe
    cK
    cY
    osumcllem.a
    osumcllem.o
    pnonsingN
    3adant3
    sseqtrd
    @11
    ss0b
    sylib
    adantr
    nsyl3
    @10
    @12
    @7
    @5
    @10
    @7
    @5
    wceq
    #
    @6
    @5
    cY
    wcel
    #
    wa
    @12
    @10
    @16
    @17
    @6
    @10
    @8
    @16
    @17
    @4
    @6
    @8
    simprr
    @7
    @5
    cY
    eleq1
    syl5ibcom
    @4
    @6
    @8
    simprl
    jctild
    @5
    cX
    cY
    elin
    syl6ibr
    necon3bd
    mpd
end
