include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "wss.mm"
include "csn.mm"
include "wcel.mm"
include "wb.mm"
include "lssne0.mm"
include "syl.mm"
include "mpbid.mm"
include "w3a.mm"
include "clspn.mm"
include "cfv.mm"
include "clmod.mm"
include "cbs.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eqid.mm"
include "lssel.mm"
include "syl2anc.mm"
include "simp3.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "lspsnel5a.mm"
include "sseq1.mm"
include "rspcev.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem lssatomic
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cU: class U
  let cW: class W
  let c.0: class .0.
  let vq: setvar q
  let vx: setvar x
  assume lssatomic.s: |- S = ( LSubSp ` W )
  assume lssatomic.o: |- .0. = ( 0g ` W )
  assume lssatomic.a: |- A = ( LSAtoms ` W )
  assume lssatomic.w: |- ( ph -> W e. LMod )
  assume lssatomic.u: |- ( ph -> U e. S )
  assume lssatomic.n: |- ( ph -> U =/= { .0. } )

  disjoint A q
  disjoint U q
  disjoint W q
  disjoint q x
  disjoint A x
  disjoint .0. x
  disjoint U x
  disjoint ph x
  assert |- ( ph -> E. q e. A q C_ U )

  proof
    wph
    vx
    cv
    #
    c.0
    wne
    #
    vx
    cU
    wrex
    #
    vq
    cv
    #
    cU
    wss
    #
    vq
    cA
    wrex
    #
    wph
    cU
    c.0
    csn
    wne
    #
    @2
    lssatomic.n
    wph
    cU
    cS
    wcel
    #
    @6
    @2
    wb
    lssatomic.u
    vx
    cS
    cW
    cU
    c.0
    lssatomic.o
    lssatomic.s
    lssne0
    syl
    mpbid
    wph
    @1
    @5
    vx
    cU
    wph
    @0
    cU
    wcel
    #
    @1
    w3a
    #
    @0
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    cA
    wcel
    #
    @11
    cU
    wss
    #
    @5
    @9
    cW
    clmod
    wcel
    #
    @0
    cW
    cbs
    cfv
    #
    wcel
    #
    @1
    @12
    wph
    @8
    @14
    @1
    lssatomic.w
    3ad2ant1
    #
    @9
    @7
    @8
    @16
    wph
    @8
    @7
    @1
    lssatomic.u
    3ad2ant1
    #
    wph
    @8
    @1
    simp2
    #
    cS
    cU
    @15
    cW
    @0
    @15
    eqid
    #
    lssatomic.s
    lssel
    syl2anc
    wph
    @8
    @1
    simp3
    cA
    @10
    @15
    cW
    @0
    c.0
    @20
    @10
    eqid
    #
    lssatomic.o
    lssatomic.a
    lsatlspsn2
    syl3anc
    @9
    cS
    cU
    @10
    cW
    @0
    lssatomic.s
    @21
    @17
    @18
    @19
    lspsnel5a
    @4
    @13
    vq
    @11
    cA
    @3
    @11
    cU
    sseq1
    rspcev
    syl2anc
    rexlimdv3a
    mpd
end
