include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "cin.mm"
include "csn.mm"
include "wceq.mm"
include "wne.mm"
include "wrex.mm"
include "wa.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "chlt.mm"
include "lssss.mm"
include "syl.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "lssincl.mm"
include "simpr.mm"
include "lssatomic.mm"
include "ex.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "dochexmidlem4.mm"
include "rexlimdv3a.mm"
include "syld.mm"
include "necon1bd.mm"
include "mpd.mm"

theorem dochexmidlem5
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  let vq: setvar q
  assume dochexmidlem1.h: |- H = ( LHyp ` K )
  assume dochexmidlem1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochexmidlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochexmidlem1.v: |- V = ( Base ` U )
  assume dochexmidlem1.s: |- S = ( LSubSp ` U )
  assume dochexmidlem1.n: |- N = ( LSpan ` U )
  assume dochexmidlem1.p: |- .(+) = ( LSSum ` U )
  assume dochexmidlem1.a: |- A = ( LSAtoms ` U )
  assume dochexmidlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochexmidlem1.x: |- ( ph -> X e. S )
  assume dochexmidlem5.pp: |- ( ph -> p e. A )
  assume dochexmidlem5.z: |- .0. = ( 0g ` U )
  assume dochexmidlem5.m: |- M = ( X .(+) p )
  assume dochexmidlem5.xn: |- ( ph -> X =/= { .0. } )
  assume dochexmidlem5.pl: |- ( ph -> -. p C_ ( X .(+) ( ._|_ ` X ) ) )


  assert |- ( ph -> ( ( ._|_ ` X ) i^i M ) = { .0. } )

  proof
    wph
    vp
    cv
    #
    cX
    cX
    c.pe
    cfv
    #
    c.po
    co
    wss
    #
    wn
    @1
    cM
    cin
    #
    c.0
    csn
    #
    wceq
    dochexmidlem5.pl
    wph
    @2
    @3
    @4
    wph
    @3
    @4
    wne
    #
    vq
    cv
    #
    @3
    wss
    #
    vq
    cA
    wrex
    #
    @2
    wph
    @5
    @8
    wph
    @5
    wa
    cA
    cS
    @3
    cU
    c.0
    vq
    dochexmidlem1.s
    dochexmidlem5.z
    dochexmidlem1.a
    wph
    cU
    clmod
    wcel
    #
    @5
    wph
    cU
    cH
    cK
    cW
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.k
    dvhlmod
    #
    adantr
    wph
    @3
    cS
    wcel
    #
    @5
    wph
    @9
    @1
    cS
    wcel
    #
    cM
    cS
    wcel
    @11
    @10
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
    wss
    #
    @12
    dochexmidlem1.k
    wph
    cX
    cS
    wcel
    #
    @14
    dochexmidlem1.x
    cS
    cX
    cV
    cU
    dochexmidlem1.v
    dochexmidlem1.s
    lssss
    syl
    cS
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.o
    dochlss
    syl2anc
    wph
    cM
    cX
    @0
    c.po
    co
    #
    cS
    dochexmidlem5.m
    wph
    @9
    @15
    @0
    cS
    wcel
    @16
    cS
    wcel
    @10
    dochexmidlem1.x
    wph
    cA
    cS
    @0
    cU
    dochexmidlem1.s
    dochexmidlem1.a
    @10
    dochexmidlem5.pp
    lsatlssel
    c.po
    cS
    cX
    @0
    cU
    dochexmidlem1.s
    dochexmidlem1.p
    lsmcl
    syl3anc
    syl5eqel
    cS
    @1
    cM
    cU
    dochexmidlem1.s
    lssincl
    syl3anc
    adantr
    wph
    @5
    simpr
    lssatomic
    ex
    wph
    @7
    @2
    vq
    cA
    wph
    @6
    cA
    wcel
    #
    @7
    w3a
    cA
    c.po
    cS
    cU
    cH
    cK
    cM
    cN
    c.pe
    cV
    cW
    cX
    c.0
    vq
    vp
    dochexmidlem1.h
    dochexmidlem1.o
    dochexmidlem1.u
    dochexmidlem1.v
    dochexmidlem1.s
    dochexmidlem1.n
    dochexmidlem1.p
    dochexmidlem1.a
    wph
    @17
    @13
    @7
    dochexmidlem1.k
    3ad2ant1
    wph
    @17
    @15
    @7
    dochexmidlem1.x
    3ad2ant1
    wph
    @17
    @0
    cA
    wcel
    @7
    dochexmidlem5.pp
    3ad2ant1
    wph
    @17
    @7
    simp2
    dochexmidlem5.z
    dochexmidlem5.m
    wph
    @17
    cX
    @4
    wne
    @7
    dochexmidlem5.xn
    3ad2ant1
    wph
    @17
    @7
    simp3
    dochexmidlem4
    rexlimdv3a
    syld
    necon1bd
    mpd
end
