include "cv.mm"
include "wss.mm"
include "wn.mm"
include "wne.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lsssssubg.mm"
include "syl.mm"
include "sseldd.mm"
include "lsatlssel.mm"
include "lsmub2.mm"
include "syl2anc.mm"
include "syl6sseqr.mm"
include "chlt.mm"
include "wa.mm"
include "lssss.mm"
include "dochlss.mm"
include "lsmub1.mm"
include "sstr2.mm"
include "syl5com.mm"
include "mtod.mm"
include "wceq.mm"
include "sseq2.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "sylc.mm"

theorem dochexmidlem7
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
  assume dochexmidlem6.pp: |- ( ph -> p e. A )
  assume dochexmidlem6.z: |- .0. = ( 0g ` U )
  assume dochexmidlem6.m: |- M = ( X .(+) p )
  assume dochexmidlem6.xn: |- ( ph -> X =/= { .0. } )
  assume dochexmidlem6.c: |- ( ph -> ( ._|_ ` ( ._|_ ` X ) ) = X )
  assume dochexmidlem6.pl: |- ( ph -> -. p C_ ( X .(+) ( ._|_ ` X ) ) )


  assert |- ( ph -> M =/= X )

  proof
    wph
    vp
    cv
    #
    cM
    wss
    #
    @0
    cX
    wss
    #
    wn
    cM
    cX
    wne
    wph
    @0
    cX
    @0
    c.po
    co
    #
    cM
    wph
    cX
    cU
    csubg
    cfv
    #
    wcel
    #
    @0
    @4
    wcel
    @0
    @3
    wss
    wph
    cS
    @4
    cX
    wph
    cU
    clmod
    wcel
    cS
    @4
    wss
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
    cS
    cU
    dochexmidlem1.s
    lsssssubg
    syl
    #
    dochexmidlem1.x
    sseldd
    #
    wph
    cS
    @4
    @0
    @7
    wph
    cA
    cS
    @0
    cU
    dochexmidlem1.s
    dochexmidlem1.a
    @6
    dochexmidlem6.pp
    lsatlssel
    sseldd
    c.po
    cX
    @0
    cU
    dochexmidlem1.p
    lsmub2
    syl2anc
    dochexmidlem6.m
    syl6sseqr
    wph
    @2
    @0
    cX
    cX
    c.pe
    cfv
    #
    c.po
    co
    #
    wss
    #
    dochexmidlem6.pl
    wph
    cX
    @10
    wss
    #
    @2
    @11
    wph
    @5
    @9
    @4
    wcel
    @12
    @8
    wph
    cS
    @4
    @9
    @7
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cV
    wss
    #
    @9
    cS
    wcel
    dochexmidlem1.k
    wph
    cX
    cS
    wcel
    @13
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
    sseldd
    c.po
    cX
    @9
    cU
    dochexmidlem1.p
    lsmub1
    syl2anc
    @0
    cX
    @10
    sstr2
    syl5com
    mtod
    @1
    @2
    cM
    cX
    cM
    cX
    wceq
    @1
    @2
    cM
    cX
    @0
    sseq2
    biimpcd
    necon3bd
    sylc
end
