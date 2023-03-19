include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wn.mm"
include "wne.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "pnonsingN.mm"
include "adantr.mm"
include "nsyl3.mm"
include "weq.mm"
include "simprr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "simprl.mm"
include "jctild.mm"
include "elin.mm"
include "syl6ibr.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem pexmidlem1N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )


  assert |- ( ( ( K e. HL /\ X C_ A ) /\ ( r e. X /\ q e. ( ._|_ ` X ) ) ) -> q =/= r )

  proof
    cK
    chlt
    wcel
    cX
    cA
    wss
    wa
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
    cX
    c.pe
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    @1
    cX
    @4
    cin
    #
    wcel
    #
    wn
    @3
    @1
    wne
    @9
    @8
    c0
    wceq
    #
    @7
    @8
    @1
    n0i
    @0
    @10
    @6
    cA
    c.pe
    cK
    cX
    pexmidlem.a
    pexmidlem.o
    pnonsingN
    adantr
    nsyl3
    @7
    @9
    @3
    @1
    @7
    vq
    vr
    weq
    #
    @2
    @1
    @4
    wcel
    #
    wa
    @9
    @7
    @11
    @12
    @2
    @7
    @5
    @11
    @12
    @0
    @2
    @5
    simprr
    @3
    @1
    @4
    eleq1
    syl5ibcom
    @0
    @2
    @5
    simprl
    jctild
    @1
    cX
    @4
    elin
    syl6ibr
    necon3bd
    mpd
end
