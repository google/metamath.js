include "cv.mm"
include "wss.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "cfv.mm"
include "dvhlmod.mm"
include "lsatlssel.mm"
include "cin.mm"
include "inss2.mm"
include "syl6ss.mm"
include "syl6sseq.mm"
include "lsmsat.mm"
include "wcel.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "inss1.mm"
include "simp3l.mm"
include "simp3r.mm"
include "dochexmidlem3.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem dochexmidlem4
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
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
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
  assume dochexmidlem4.pp: |- ( ph -> p e. A )
  assume dochexmidlem4.qq: |- ( ph -> q e. A )
  assume dochexmidlem4.z: |- .0. = ( 0g ` U )
  assume dochexmidlem4.m: |- M = ( X .(+) p )
  assume dochexmidlem4.xn: |- ( ph -> X =/= { .0. } )
  assume dochexmidlem4.pl: |- ( ph -> q C_ ( ( ._|_ ` X ) i^i M ) )


  assert |- ( ph -> p C_ ( X .(+) ( ._|_ ` X ) ) )

  proof
    wph
    vr
    cv
    #
    cX
    wss
    #
    vq
    cv
    #
    @0
    vp
    cv
    #
    c.po
    co
    wss
    #
    wa
    #
    vr
    cA
    wrex
    @3
    cX
    cX
    c.pe
    cfv
    #
    c.po
    co
    wss
    #
    wph
    cA
    c.po
    @2
    cS
    cX
    @3
    cU
    c.0
    vr
    dochexmidlem4.z
    dochexmidlem1.s
    dochexmidlem1.p
    dochexmidlem1.a
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
    dochexmidlem1.x
    wph
    cA
    cS
    @3
    cU
    dochexmidlem1.s
    dochexmidlem1.a
    @8
    dochexmidlem4.pp
    lsatlssel
    dochexmidlem4.qq
    dochexmidlem4.xn
    wph
    @2
    cM
    cX
    @3
    c.po
    co
    wph
    @2
    @6
    cM
    cin
    #
    cM
    dochexmidlem4.pl
    @6
    cM
    inss2
    syl6ss
    dochexmidlem4.m
    syl6sseq
    lsmsat
    wph
    @5
    @7
    vr
    cA
    wph
    @0
    cA
    wcel
    #
    @5
    w3a
    cA
    c.po
    cS
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    cX
    vr
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
    @10
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @5
    dochexmidlem1.k
    3ad2ant1
    wph
    @10
    cX
    cS
    wcel
    @5
    dochexmidlem1.x
    3ad2ant1
    wph
    @10
    @3
    cA
    wcel
    @5
    dochexmidlem4.pp
    3ad2ant1
    wph
    @10
    @2
    cA
    wcel
    @5
    dochexmidlem4.qq
    3ad2ant1
    wph
    @10
    @5
    simp2
    wph
    @10
    @2
    @6
    wss
    @5
    wph
    @2
    @9
    @6
    dochexmidlem4.pl
    @6
    cM
    inss1
    syl6ss
    3ad2ant1
    wph
    @10
    @1
    @4
    simp3l
    wph
    @10
    @1
    @4
    simp3r
    dochexmidlem3
    rexlimdv3a
    mpd
end
