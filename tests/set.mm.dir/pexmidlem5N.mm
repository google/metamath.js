include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wn.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "n0.mm"
include "pexmidlem4N.mm"
include "expr.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "necon1bd.mm"
include "impr.mm"

theorem pexmidlem5N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )


  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( X =/= (/) /\ -. p e. ( X .+ ( ._|_ ` X ) ) ) ) -> ( ( ._|_ ` X ) i^i M ) = (/) )

  proof
    cK
    chlt
    wcel
    cX
    cA
    wss
    vp
    cv
    #
    cA
    wcel
    w3a
    #
    cX
    c0
    wne
    #
    @0
    cX
    cX
    c.pe
    cfv
    #
    c.pl
    co
    wcel
    #
    wn
    @3
    cM
    cin
    #
    c0
    wceq
    @1
    @2
    wa
    #
    @4
    @5
    c0
    @5
    c0
    wne
    vq
    cv
    @5
    wcel
    #
    vq
    wex
    @6
    @4
    vq
    @5
    n0
    @6
    @7
    @4
    vq
    @1
    @2
    @7
    @4
    cA
    c.pl
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    vq
    vp
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    pexmidlem.o
    pexmidlem.m
    pexmidlem4N
    expr
    exlimdv
    syl5bi
    necon1bd
    impr
end
