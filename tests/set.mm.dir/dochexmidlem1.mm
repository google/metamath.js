include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wss.mm"
include "wn.mm"
include "wne.mm"
include "c0g.mm"
include "csn.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lsatn0.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "lsatlssel.mm"
include "lssle0.mm"
include "syl2anc.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "chlt.mm"
include "wa.mm"
include "dochnoncon.mm"
include "sseq2d.mm"
include "mtbird.mm"
include "weq.mm"
include "sseq1.mm"
include "syl5ibcom.mm"
include "jctild.mm"
include "ssin.mm"
include "syl6ib.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem dochexmidlem1
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vq: setvar q
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
  assume dochexmidlem1.pp: |- ( ph -> p e. A )
  assume dochexmidlem1.qq: |- ( ph -> q e. A )
  assume dochexmidlem1.rr: |- ( ph -> r e. A )
  assume dochexmidlem1.ql: |- ( ph -> q C_ ( ._|_ ` X ) )
  assume dochexmidlem1.rl: |- ( ph -> r C_ X )


  assert |- ( ph -> q =/= r )

  proof
    wph
    vr
    cv
    #
    cX
    cX
    c.pe
    cfv
    #
    cin
    #
    wss
    #
    wn
    vq
    cv
    #
    @0
    wne
    wph
    @3
    @0
    cU
    c0g
    cfv
    #
    csn
    #
    wss
    #
    wph
    @7
    wn
    @0
    @6
    wne
    wph
    cA
    @0
    cU
    @5
    @5
    eqid
    #
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
    dochexmidlem1.rr
    lsatn0
    wph
    @7
    @0
    @6
    wph
    cU
    clmod
    wcel
    @0
    cS
    wcel
    @7
    @0
    @6
    wceq
    wb
    @9
    wph
    cA
    cS
    @0
    cU
    dochexmidlem1.s
    dochexmidlem1.a
    @9
    dochexmidlem1.rr
    lsatlssel
    cS
    cU
    @0
    @5
    @8
    dochexmidlem1.s
    lssle0
    syl2anc
    necon3bbid
    mpbird
    wph
    @2
    @6
    @0
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cS
    wcel
    @2
    @6
    wceq
    dochexmidlem1.k
    dochexmidlem1.x
    cS
    cU
    cH
    cK
    c.pe
    cW
    cX
    @5
    dochexmidlem1.h
    dochexmidlem1.u
    dochexmidlem1.s
    @8
    dochexmidlem1.o
    dochnoncon
    syl2anc
    sseq2d
    mtbird
    wph
    @3
    @4
    @0
    wph
    vq
    vr
    weq
    #
    @0
    cX
    wss
    #
    @0
    @1
    wss
    #
    wa
    @3
    wph
    @10
    @12
    @11
    wph
    @4
    @1
    wss
    @10
    @12
    dochexmidlem1.ql
    @4
    @0
    @1
    sseq1
    syl5ibcom
    dochexmidlem1.rl
    jctild
    @0
    cX
    @1
    ssin
    syl6ib
    necon3bd
    mpd
end
