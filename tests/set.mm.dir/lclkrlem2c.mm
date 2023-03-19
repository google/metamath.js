include "csn.mm"
include "cfv.mm"
include "cin.mm"
include "co.mm"
include "cdjh.mm"
include "cdih.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "eldifad.mm"
include "dihlsprn.mm"
include "syl2anc.mm"
include "dvhlmod.mm"
include "lsatlspsn.mm"
include "dihsmatrn.mm"
include "wss.mm"
include "snssd.mm"
include "dochcl.mm"
include "dochdmm1.mm"
include "cun.mm"
include "cpr.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "lsmpr.mm"
include "syl5reqr.mm"
include "fveq2d.mm"
include "unssd.mm"
include "dochocsp.mm"
include "wceq.mm"
include "dochdmj1.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "dochocsn.mm"
include "oveq12d.mm"
include "dihmeetcl.mm"
include "syl12anc.mm"
include "dihjat1.mm"
include "3eqtrrd.mm"
include "lclkrlem2b.mm"
include "dochsatshp.mm"
include "eqeltrd.mm"

theorem lclkrlem2c
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cJ: class J
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
  assume lclkrlem2c.j: |- J = ( LSHyp ` U )


  assert |- ( ph -> ( ( ( ._|_ ` { X } ) i^i ( ._|_ ` { Y } ) ) .(+) ( N ` { B } ) ) e. J )

  proof
    wph
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
    cB
    csn
    #
    cN
    cfv
    #
    c.po
    co
    #
    @0
    cN
    cfv
    #
    @2
    cN
    cfv
    #
    c.po
    co
    #
    @5
    c.pe
    cfv
    #
    cin
    #
    c.pe
    cfv
    #
    cJ
    wph
    @13
    @10
    c.pe
    cfv
    #
    @11
    c.pe
    cfv
    #
    cW
    cK
    cdjh
    cfv
    cfv
    #
    co
    @4
    @6
    @16
    co
    @7
    wph
    cU
    cH
    cW
    cK
    cdih
    cfv
    cfv
    #
    @16
    cK
    c.pe
    cV
    cW
    @10
    @11
    lclkrlem2a.h
    @17
    eqid
    #
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    @16
    eqid
    #
    lclkrlem2a.k
    wph
    cA
    c.po
    @9
    cU
    cH
    @17
    cK
    cW
    @8
    lclkrlem2a.h
    @18
    lclkrlem2a.u
    lclkrlem2a.p
    lclkrlem2a.a
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
    @8
    @17
    crn
    #
    wcel
    lclkrlem2a.k
    wph
    cX
    cV
    c.0
    csn
    #
    lclkrlem2a.x
    eldifad
    #
    cU
    cH
    @17
    cK
    cN
    cV
    cW
    cX
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.n
    @18
    dihlsprn
    syl2anc
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
    lclkrlem2a.y
    lsatlspsn
    dihsmatrn
    wph
    @20
    @5
    cV
    wss
    @11
    @21
    wcel
    lclkrlem2a.k
    wph
    cB
    cV
    wph
    cB
    cV
    @22
    lclkrlem2a.b
    eldifad
    #
    snssd
    cU
    cH
    @17
    cK
    c.pe
    cV
    cW
    @5
    lclkrlem2a.h
    @18
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochcl
    syl2anc
    dochdmm1
    wph
    @14
    @4
    @15
    @6
    @16
    wph
    @14
    @0
    @2
    cun
    #
    cN
    cfv
    #
    c.pe
    cfv
    @26
    c.pe
    cfv
    #
    @4
    wph
    @10
    @27
    c.pe
    wph
    @27
    cX
    cY
    cpr
    #
    cN
    cfv
    @10
    @29
    @26
    cN
    cX
    cY
    df-pr
    fveq2i
    wph
    c.po
    cN
    cV
    cU
    cX
    cY
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.p
    @24
    @23
    wph
    cY
    cV
    @22
    lclkrlem2a.y
    eldifad
    #
    lsmpr
    syl5reqr
    fveq2d
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @26
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.o
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.k
    wph
    @0
    @2
    cV
    wph
    cX
    cV
    @23
    snssd
    #
    wph
    cY
    cV
    @30
    snssd
    #
    unssd
    dochocsp
    wph
    @20
    @0
    cV
    wss
    #
    @2
    cV
    wss
    #
    @28
    @4
    wceq
    lclkrlem2a.k
    @31
    @32
    cU
    cH
    cK
    c.pe
    cV
    cW
    @0
    @2
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochdmj1
    syl3anc
    3eqtrd
    wph
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cB
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.o
    lclkrlem2a.v
    lclkrlem2a.n
    lclkrlem2a.k
    @25
    dochocsn
    oveq12d
    wph
    c.po
    cB
    cU
    cH
    @17
    @16
    cK
    cN
    cV
    cW
    @4
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.p
    lclkrlem2a.n
    @18
    @19
    lclkrlem2a.k
    wph
    @20
    @1
    @21
    wcel
    #
    @3
    @21
    wcel
    #
    @4
    @21
    wcel
    lclkrlem2a.k
    wph
    @20
    @33
    @35
    lclkrlem2a.k
    @31
    cU
    cH
    @17
    cK
    c.pe
    cV
    cW
    @0
    lclkrlem2a.h
    @18
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochcl
    syl2anc
    wph
    @20
    @34
    @36
    lclkrlem2a.k
    @32
    cU
    cH
    @17
    cK
    c.pe
    cV
    cW
    @2
    lclkrlem2a.h
    @18
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.o
    dochcl
    syl2anc
    cH
    @17
    cK
    cW
    @1
    @3
    lclkrlem2a.h
    @18
    dihmeetcl
    syl12anc
    @25
    dihjat1
    3eqtrrd
    wph
    cA
    @12
    cU
    cH
    cK
    c.pe
    cW
    cJ
    lclkrlem2a.h
    lclkrlem2a.u
    lclkrlem2a.o
    lclkrlem2a.a
    lclkrlem2c.j
    lclkrlem2a.k
    wph
    cA
    cB
    c.po
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    cY
    c.0
    lclkrlem2a.h
    lclkrlem2a.o
    lclkrlem2a.u
    lclkrlem2a.v
    lclkrlem2a.z
    lclkrlem2a.p
    lclkrlem2a.n
    lclkrlem2a.a
    lclkrlem2a.k
    lclkrlem2a.b
    lclkrlem2a.x
    lclkrlem2a.y
    lclkrlem2a.e
    lclkrlem2b.da
    lclkrlem2b
    dochsatshp
    eqeltrd
end
