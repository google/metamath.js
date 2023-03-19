include "cv.mm"
include "ctp.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "cpr.mm"
include "dvh4dimlem.mm"
include "clmod.mm"
include "wss.mm"
include "dvhlmod.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "prssi.mm"
include "syl2anc.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "ssneld.mm"
include "reximdv.mm"
include "mpd.mm"

theorem dvhdimlem
  let wph: wff ph
  let vz: setvar z
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vp: setvar p
  let cZ: class Z
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvhdim.y: |- ( ph -> Y e. V )
  assume dvhdim.o: |- .0. = ( 0g ` U )
  assume dvhdim.x: |- ( ph -> X =/= .0. )
  assume dvhdimlem.y: |- ( ph -> Y =/= .0. )

  disjoint N z
  disjoint .0. z
  disjoint U z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint ph z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint .0. p
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  disjoint Z z
  disjoint p ph
  assert |- ( ph -> E. z e. V -. z e. ( N ` { X , Y } ) )

  proof
    wph
    vz
    cv
    #
    cX
    cY
    cY
    ctp
    #
    cN
    cfv
    #
    wcel
    wn
    #
    vz
    cV
    wrex
    @0
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    wn
    #
    vz
    cV
    wrex
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cX
    cY
    c.0
    cY
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.x
    dvhdim.y
    dvhdim.y
    dvhdim.o
    dvhdim.x
    dvhdimlem.y
    dvhdimlem.y
    dvh4dimlem
    wph
    @3
    @6
    vz
    cV
    wph
    @5
    @2
    @0
    wph
    cU
    clmod
    wcel
    @1
    cV
    wss
    @4
    @1
    wss
    #
    @5
    @2
    wss
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    wph
    @1
    @4
    cY
    csn
    #
    cun
    #
    cV
    cX
    cY
    cY
    df-tp
    #
    wph
    @4
    @8
    cV
    wph
    cX
    cV
    wcel
    cY
    cV
    wcel
    @4
    cV
    wss
    dvh3dim.x
    dvhdim.y
    cX
    cY
    cV
    prssi
    syl2anc
    wph
    cY
    cV
    dvhdim.y
    snssd
    unssd
    syl5eqss
    @7
    wph
    @4
    @9
    @1
    @4
    @8
    ssun1
    @10
    sseqtr4i
    a1i
    @4
    @1
    cN
    cV
    cU
    dvh3dim.v
    dvh3dim.n
    lspss
    syl3anc
    ssneld
    reximdv
    mpd
end
