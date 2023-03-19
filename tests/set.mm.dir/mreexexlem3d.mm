include "cpw.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "cun.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "simpr.mm"
include "wss.mm"
include "cdif.mm"
include "cin.mm"
include "cmre.mm"
include "cfv.mm"
include "adantr.mm"
include "uneq1d.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sseqtrd.mm"
include "mrissd.mm"
include "unssbd.mm"
include "mrcssidd.mm"
include "unssd.mm"
include "ssun2.mm"
include "a1i.mm"
include "mrissmrcd.mm"
include "ssequn1.mm"
include "sylibr.mm"
include "ssind.mm"
include "disjdif.mm"
include "syl6sseq.mm"
include "ss0b.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "0elpw.mm"
include "syl6eqel.mm"
include "cvv.mm"
include "elfvexd.mm"
include "difss2d.mm"
include "ssexd.mm"
include "enrefg.mm"
include "syl.mm"
include "breq2.mm"
include "uneq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem mreexexlem3d
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume mreexexlem2d.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexexlem2d.2: |- N = ( mrCls ` A )
  assume mreexexlem2d.3: |- I = ( mrInd ` A )
  assume mreexexlem2d.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexexlem2d.5: |- ( ph -> F C_ ( X \ H ) )
  assume mreexexlem2d.6: |- ( ph -> G C_ ( X \ H ) )
  assume mreexexlem2d.7: |- ( ph -> F C_ ( N ` ( G u. H ) ) )
  assume mreexexlem2d.8: |- ( ph -> ( F u. H ) e. I )
  assume mreexexlem3d.9: |- ( ph -> ( F = (/) \/ G = (/) ) )

  disjoint F i
  disjoint G i
  disjoint H i
  disjoint I i
  assert |- ( ph -> E. i e. ~P G ( F ~~ i /\ ( i u. H ) e. I ) )

  proof
    wph
    cF
    cG
    cpw
    #
    wcel
    cF
    cF
    cen
    wbr
    #
    cF
    cH
    cun
    #
    cI
    wcel
    #
    cF
    vi
    cv
    #
    cen
    wbr
    #
    @4
    cH
    cun
    #
    cI
    wcel
    #
    wa
    #
    vi
    @0
    wrex
    wph
    cF
    c0
    @0
    wph
    cF
    c0
    wceq
    #
    @9
    cG
    c0
    wceq
    #
    wph
    @9
    simpr
    wph
    @10
    wa
    #
    cF
    c0
    wss
    @9
    @11
    cF
    cH
    cX
    cH
    cdif
    #
    cin
    c0
    @11
    cF
    cH
    @12
    @11
    @2
    cH
    wceq
    cF
    cH
    wss
    @11
    cA
    @2
    cH
    cI
    cN
    cX
    wph
    cA
    cX
    cmre
    cfv
    wcel
    @10
    mreexexlem2d.1
    adantr
    #
    mreexexlem2d.2
    mreexexlem2d.3
    @11
    cF
    cH
    cH
    cN
    cfv
    #
    @11
    cF
    cG
    cH
    cun
    #
    cN
    cfv
    #
    @14
    wph
    cF
    @16
    wss
    @10
    mreexexlem2d.7
    adantr
    @11
    @15
    cH
    cN
    @11
    @15
    c0
    cH
    cun
    #
    cH
    @11
    cG
    c0
    cH
    wph
    @10
    simpr
    uneq1d
    cH
    c0
    cun
    @17
    cH
    cH
    c0
    uncom
    cH
    un0
    eqtr3i
    syl6eq
    fveq2d
    sseqtrd
    @11
    cA
    cH
    cN
    cX
    @13
    mreexexlem2d.2
    @11
    cF
    cH
    cX
    @11
    cA
    @2
    cI
    cX
    mreexexlem2d.3
    @13
    wph
    @3
    @10
    mreexexlem2d.8
    adantr
    #
    mrissd
    unssbd
    mrcssidd
    unssd
    cH
    @2
    wss
    @11
    cH
    cF
    ssun2
    a1i
    @18
    mrissmrcd
    cF
    cH
    ssequn1
    sylibr
    wph
    cF
    @12
    wss
    @10
    mreexexlem2d.5
    adantr
    ssind
    cH
    cX
    disjdif
    syl6sseq
    cF
    ss0b
    sylib
    mreexexlem3d.9
    mpjaodan
    cG
    0elpw
    syl6eqel
    wph
    cF
    cvv
    wcel
    @1
    wph
    cF
    cX
    cvv
    wph
    cA
    cmre
    cX
    mreexexlem2d.1
    elfvexd
    wph
    cF
    cX
    cH
    mreexexlem2d.5
    difss2d
    ssexd
    cF
    cvv
    enrefg
    syl
    mreexexlem2d.8
    @8
    @1
    @3
    wa
    vi
    cF
    @0
    @4
    cF
    wceq
    #
    @5
    @1
    @7
    @3
    @4
    cF
    cF
    cen
    breq2
    @19
    @6
    @2
    cI
    @4
    cF
    cH
    uneq1
    eleq1d
    anbi12d
    rspcev
    syl12anc
end
