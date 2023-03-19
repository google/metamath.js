include "csn.mm"
include "cfv.mm"
include "clss.mm"
include "clsh.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "dochsnshp.mm"
include "dvhlmod.mm"
include "lsatlspsn.mm"
include "wne.mm"
include "wceq.mm"
include "eldifad.mm"
include "snssd.mm"
include "dochocsp.mm"
include "eqeq12d.mm"
include "cdih.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "doch11.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "wss.mm"
include "dochlss.mm"
include "lspsnel5.mm"
include "mtbid.mm"
include "lshpat.mm"

theorem lclkrlem2a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.po: class .(+)
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
  assume lclkrlem2a.d: |- ( ph -> -. X e. ( ._|_ ` { B } ) )


  assert |- ( ph -> ( ( ( N ` { X } ) .(+) ( N ` { Y } ) ) i^i ( ._|_ ` { B } ) ) e. A )

  proof
    wph
    cA
    c.po
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    cU
    clss
    cfv
    #
    cB
    csn
    #
    c.pe
    cfv
    #
    cU
    clsh
    cfv
    #
    cU
    @4
    eqid
    #
    lclkrlem2a.p
    @7
    eqid
    #
    lclkrlem2a.a
    wph
    cU
    cH
    cK
    cW
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.k
    dvhlvec
    wph
    cU
    cH
    cK
    c.pe
    cV
    cW
    cB
    @7
    c.0
    lclkrlem2a.h
    lclkrlem2a.o
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.z
    @9
    lclkrlem2a.k
    lclkrlem2a.b
    dochsnshp
    wph
    cA
    cN
    cV
    cU
    cX
    c.0
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.z
    lclkrlem2a.a
    wph
    cU
    cH
    cK
    cW
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.k
    dvhlmod
    #
    lclkrlem2a.x
    lsatlspsn
    wph
    cA
    cN
    cV
    cU
    cY
    c.0
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.z
    lclkrlem2a.a
    @10
    lclkrlem2a.y
    lsatlspsn
    wph
    @0
    c.pe
    cfv
    #
    @2
    c.pe
    cfv
    #
    wne
    @1
    @3
    wne
    lclkrlem2a.e
    wph
    @11
    @12
    @1
    @3
    wph
    @1
    c.pe
    cfv
    #
    @3
    c.pe
    cfv
    #
    wceq
    @11
    @12
    wceq
    @1
    @3
    wceq
    wph
    @13
    @11
    @14
    @12
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @0
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.o
    lclkrlem2a.v
    lclkrlem2a.n
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
    #
    snssd
    dochocsp
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @2
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.o
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.k
    wph
    cY
    cV
    wph
    cY
    cV
    @15
    lclkrlem2a.y
    eldifad
    #
    snssd
    dochocsp
    eqeq12d
    wph
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    cK
    c.pe
    cW
    @1
    @3
    lclkrlem2a.h
    @18
    eqid
    #
    lclkrlem2a.o
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
    cX
    cV
    wcel
    @1
    @18
    crn
    #
    wcel
    lclkrlem2a.k
    @16
    cU
    cH
    @18
    cK
    cN
    cV
    cW
    cX
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.n
    @19
    dihlsprn
    syl2anc
    wph
    @20
    cY
    cV
    wcel
    @3
    @21
    wcel
    lclkrlem2a.k
    @17
    cU
    cH
    @18
    cK
    cN
    cV
    cW
    cY
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.n
    @19
    dihlsprn
    syl2anc
    doch11
    bitr3d
    necon3bid
    mpbid
    wph
    cX
    @6
    wcel
    @1
    @6
    wss
    lclkrlem2a.d
    wph
    @4
    @6
    cN
    cV
    cU
    cX
    lclkrlem2a.v
    @8
    lclkrlem2a.n
    @10
    wph
    @20
    @5
    cV
    wss
    @6
    @4
    wcel
    lclkrlem2a.k
    wph
    cB
    cV
    wph
    cB
    cV
    @15
    lclkrlem2a.b
    eldifad
    snssd
    @4
    cU
    cH
    cK
    c.pe
    cV
    cW
    @5
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    @8
    lclkrlem2a.o
    dochlss
    syl2anc
    @16
    lspsnel5
    mtbid
    lshpat
end
