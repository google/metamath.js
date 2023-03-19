include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochdmj1.mm"
include "syl3anc.mm"
include "syl5eq.mm"

theorem lcfrlem18
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lcfrlem17.h: |- H = ( LHyp ` K )
  assume lcfrlem17.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem17.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem17.v: |- V = ( Base ` U )
  assume lcfrlem17.p: |- .+ = ( +g ` U )
  assume lcfrlem17.z: |- .0. = ( 0g ` U )
  assume lcfrlem17.n: |- N = ( LSpan ` U )
  assume lcfrlem17.a: |- A = ( LSAtoms ` U )
  assume lcfrlem17.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem17.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lcfrlem17.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lcfrlem17.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( ._|_ ` { X , Y } ) = ( ( ._|_ ` { X } ) i^i ( ._|_ ` { Y } ) ) )

  proof
    wph
    cX
    cY
    cpr
    #
    c.pe
    cfv
    cX
    csn
    #
    cY
    csn
    #
    cun
    #
    c.pe
    cfv
    #
    @1
    c.pe
    cfv
    @2
    c.pe
    cfv
    cin
    #
    @0
    @3
    c.pe
    cX
    cY
    df-pr
    fveq2i
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @1
    cV
    wss
    @2
    cV
    wss
    @4
    @5
    wceq
    lcfrlem17.k
    wph
    cX
    cV
    wph
    cX
    cV
    c.0
    csn
    #
    lcfrlem17.x
    eldifad
    snssd
    wph
    cY
    cV
    wph
    cY
    cV
    @6
    lcfrlem17.y
    eldifad
    snssd
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    @2
    lcfrlem17.h
    lcfrlem17.u
    lcfrlem17.v
    lcfrlem17.o
    dochdmj1
    syl3anc
    syl5eq
end
