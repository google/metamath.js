include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochcl.mm"
include "syl2anc.mm"
include "dihmeetcl.mm"
include "syl12anc.mm"
include "dihsmsprn.mm"

theorem lclkrlem2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2a.h: |- H = ( LHyp ` K )
  assume lclkrlem2a.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2a.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2a.v: |- V = ( Base ` U )
  assume lclkrlem2a.z: |- .0. = ( 0g ` U )
  assume lclkrlem2a.p: |- .(+) = ( LSSum ` U )
  assume lclkrlem2a.n: |- N = ( LSpan ` U )
  assume lclkrlem2a.a: |- A = ( LSAtoms ` U )
  assume lclkrlem2a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2a.b: |- ( ph -> B e. ( V \ { .0. } ) )
  assume lclkrlem2a.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume lclkrlem2a.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume lclkrlem2a.e: |- ( ph -> ( ._|_ ` { X } ) =/= ( ._|_ ` { Y } ) )
  assume lclkrlem2b.da: |- ( ph -> ( -. X e. ( ._|_ ` { B } ) \/ -. Y e. ( ._|_ ` { B } ) ) )
  assume lclkrlem2d.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ph -> ( ( ( ._|_ ` { X } ) i^i ( ._|_ ` { Y } ) ) .(+) ( N ` { B } ) ) e. ran I )

  proof
    wph
    c.po
    cB
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    csn
    #
    c.pe
    cfv
    #
    cY
    csn
    #
    c.pe
    cfv
    #
    cin
    #
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.p
    lclkrlem2a.n
    lclkrlem2d.i
    lclkrlem2a.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cI
    crn
    #
    wcel
    #
    @3
    @6
    wcel
    #
    @4
    @6
    wcel
    lclkrlem2a.k
    wph
    @5
    @0
    cV
    wss
    @7
    lclkrlem2a.k
    wph
    cX
    cV
    wph
    cX
    cV
    c.0
    csn
    #
    lclkrlem2a.x
    eldifad
    snssd
    cU
    cH
    cI
    cK
    c.pe
    cV
    cW
    @0
    lclkrlem2a.h
    lclkrlem2d.i
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochcl
    syl2anc
    wph
    @5
    @2
    cV
    wss
    @8
    lclkrlem2a.k
    wph
    cY
    cV
    wph
    cY
    cV
    @9
    lclkrlem2a.y
    eldifad
    snssd
    cU
    cH
    cI
    cK
    c.pe
    cV
    cW
    @2
    lclkrlem2a.h
    lclkrlem2d.i
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochcl
    syl2anc
    cH
    cI
    cK
    cW
    @1
    @3
    lclkrlem2a.h
    lclkrlem2d.i
    dihmeetcl
    syl12anc
    wph
    cB
    cV
    @9
    lclkrlem2a.b
    eldifad
    dihsmsprn
end
