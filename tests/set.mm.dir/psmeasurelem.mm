include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cvv.mm"
include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "simpr.mm"
include "uniiun.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wb.mm"
include "elpwg.mm"
include "mpbird.mm"
include "pwpwuni.mm"
include "mpbid.mm"
include "elpwid.mm"
include "fssresd.mm"
include "sge0iun.mm"
include "wceq.mm"
include "a1i.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "feqmptd.mm"
include "wa.mm"
include "fvres.mm"
include "sselda.mm"
include "elssuni.mm"
include "resabs1.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem psmeasurelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cH: class H
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume psmeasurelem.x: |- ( ph -> X e. V )
  assume psmeasurelem.h: |- ( ph -> H : X --> ( 0 [,] +oo ) )
  assume psmeasurelem.m: |- M = ( x e. ~P X |-> ( sum^ ` ( H |` x ) ) )
  assume psmeasurelem.mf: |- ( ph -> M : ~P X --> ( 0 [,] +oo ) )
  assume psmeasurelem.y: |- ( ph -> Y C_ ~P X )
  assume psmeasurelem.dj: |- ( ph -> Disj_ y e. Y y )

  disjoint H x
  disjoint H y
  disjoint x y
  disjoint M y
  disjoint X x
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( M ` U. Y ) = ( sum^ ` ( M |` Y ) ) )

  proof
    wph
    cH
    cY
    cuni
    #
    cres
    #
    csumge0
    cfv
    #
    vy
    cY
    @1
    vy
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    @0
    cM
    cfv
    cM
    cY
    cres
    #
    csumge0
    cfv
    wph
    vy
    cY
    @3
    @1
    cvv
    cY
    @0
    wph
    cY
    cX
    cpw
    #
    wss
    #
    @8
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    psmeasurelem.y
    wph
    cX
    cV
    wcel
    @10
    psmeasurelem.x
    cX
    cV
    pwexg
    syl
    cY
    @8
    cvv
    ssexg
    syl2anc
    #
    wph
    @3
    cY
    wcel
    #
    simpr
    #
    vy
    cY
    uniiun
    wph
    cX
    cc0
    cpnf
    cicc
    co
    #
    @0
    cH
    psmeasurelem.h
    wph
    @0
    cX
    wph
    cY
    @8
    cpw
    wcel
    #
    @0
    @8
    wcel
    #
    wph
    @16
    @9
    psmeasurelem.y
    wph
    @11
    @16
    @9
    wb
    @12
    cY
    @8
    cvv
    elpwg
    syl
    mpbird
    wph
    @11
    @16
    @17
    wb
    @12
    cY
    cX
    cvv
    pwpwuni
    syl
    mpbid
    #
    elpwid
    fssresd
    psmeasurelem.dj
    sge0iun
    wph
    vx
    @0
    cH
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    @2
    @8
    cM
    cvv
    cM
    vx
    @8
    @21
    cmpt
    wceq
    #
    wph
    psmeasurelem.m
    a1i
    @19
    @0
    wceq
    #
    @21
    @2
    wceq
    wph
    @23
    @20
    @1
    csumge0
    @19
    @0
    cH
    reseq2
    fveq2d
    adantl
    @18
    wph
    @1
    csumge0
    fvexd
    fvmptd
    wph
    @7
    @6
    csumge0
    wph
    @7
    vy
    cY
    @3
    @7
    cfv
    #
    cmpt
    @6
    wph
    vy
    cY
    @15
    @7
    wph
    @8
    @15
    cY
    cM
    psmeasurelem.mf
    psmeasurelem.y
    fssresd
    feqmptd
    wph
    vy
    cY
    @24
    @5
    wph
    @13
    wa
    #
    @24
    @3
    cM
    cfv
    #
    cH
    @3
    cres
    #
    csumge0
    cfv
    #
    @5
    @25
    @13
    @24
    @26
    wceq
    @14
    @3
    cY
    cM
    fvres
    syl
    @25
    vx
    @3
    @21
    @28
    @8
    cM
    cvv
    @22
    @25
    psmeasurelem.m
    a1i
    @19
    @3
    wceq
    #
    @21
    @28
    wceq
    @25
    @29
    @20
    @27
    csumge0
    @19
    @3
    cH
    reseq2
    fveq2d
    adantl
    wph
    cY
    @8
    @3
    psmeasurelem.y
    sselda
    @25
    @27
    csumge0
    fvexd
    fvmptd
    @25
    @27
    @4
    csumge0
    @13
    @27
    @4
    wceq
    wph
    @13
    @4
    @27
    @13
    @3
    @0
    wss
    @4
    @27
    wceq
    @3
    cY
    elssuni
    cH
    @3
    @0
    resabs1
    syl
    eqcomd
    adantl
    fveq2d
    3eqtrd
    mpteq2dva
    eqtrd
    fveq2d
    3eqtr4d
end
