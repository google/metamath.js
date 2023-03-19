include "cpw.mm"
include "clss.mm"
include "cfv.mm"
include "wf.mm"
include "c0g.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "clsh.mm"
include "wcel.mm"
include "wa.mm"
include "clsa.mm"
include "wral.mm"
include "wb.mm"
include "eqid.mm"
include "islpolN.mm"
include "syl.mm"
include "mpbid.mm"
include "simpr2.mm"
include "3jca.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "sseq1.mm"
include "biidd.mm"
include "3anbi123d.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "sseq1d.mm"
include "sylan9bb.mm"
include "spc2gv.mm"
include "syl2anc.mm"
include "mpid.mm"
include "syl5.mm"
include "mpd.mm"

theorem lpolconN
  let wph: wff ph
  let cP: class P
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume lpolcon.v: |- V = ( Base ` W )
  assume lpolcon.p: |- P = ( LPol ` W )
  assume lpolcon.w: |- ( ph -> W e. X )
  assume lpolcon.o: |- ( ph -> ._|_ e. P )
  assume lpolcon.x: |- ( ph -> X C_ V )
  assume lpolcon.y: |- ( ph -> Y C_ V )
  assume lpolcon.c: |- ( ph -> X C_ Y )


  assert |- ( ph -> ( ._|_ ` Y ) C_ ( ._|_ ` X ) )

  proof
    wph
    cV
    cpw
    #
    cW
    clss
    cfv
    #
    c.pe
    wf
    #
    cV
    c.pe
    cfv
    cW
    c0g
    cfv
    #
    csn
    wceq
    #
    vx
    cv
    #
    cV
    wss
    #
    vy
    cv
    #
    cV
    wss
    #
    @5
    @7
    wss
    #
    w3a
    #
    @7
    c.pe
    cfv
    #
    @5
    c.pe
    cfv
    #
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @12
    cW
    clsh
    cfv
    #
    wcel
    @12
    c.pe
    cfv
    @5
    wceq
    wa
    vx
    cW
    clsa
    cfv
    #
    wral
    #
    w3a
    wa
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    wss
    #
    wph
    c.pe
    cP
    wcel
    #
    @19
    lpolcon.o
    wph
    cW
    cX
    wcel
    @23
    @19
    wb
    lpolcon.w
    vx
    vy
    @17
    cP
    @1
    @16
    c.pe
    cV
    cW
    cX
    @3
    lpolcon.v
    @1
    eqid
    @3
    eqid
    @17
    eqid
    @16
    eqid
    lpolcon.p
    islpolN
    syl
    mpbid
    @19
    @15
    wph
    @22
    @2
    @4
    @15
    @18
    simpr2
    wph
    @15
    cX
    cV
    wss
    #
    cY
    cV
    wss
    #
    cX
    cY
    wss
    #
    w3a
    #
    @22
    wph
    @24
    @25
    @26
    lpolcon.x
    lpolcon.y
    lpolcon.c
    3jca
    wph
    cX
    @0
    wcel
    #
    cY
    @0
    wcel
    #
    @15
    @27
    @22
    wi
    #
    wi
    wph
    @24
    @28
    lpolcon.x
    cX
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lpolcon.v
    cW
    cbs
    fvex
    eqeltri
    #
    elpw2
    sylibr
    wph
    @25
    @29
    lpolcon.y
    cY
    cV
    @31
    elpw2
    sylibr
    @14
    @30
    vx
    vy
    cX
    cY
    @0
    @0
    @5
    cX
    wceq
    #
    @14
    @24
    @8
    cX
    @7
    wss
    #
    w3a
    #
    @11
    @21
    wss
    #
    wi
    @7
    cY
    wceq
    #
    @30
    @32
    @10
    @34
    @13
    @35
    @32
    @6
    @24
    @8
    @8
    @9
    @33
    @5
    cX
    cV
    sseq1
    @32
    @8
    biidd
    @5
    cX
    @7
    sseq1
    3anbi123d
    @32
    @12
    @21
    @11
    @5
    cX
    c.pe
    fveq2
    sseq2d
    imbi12d
    @36
    @34
    @27
    @35
    @22
    @36
    @24
    @24
    @8
    @25
    @33
    @26
    @36
    @24
    biidd
    @7
    cY
    cV
    sseq1
    @7
    cY
    cX
    sseq2
    3anbi123d
    @36
    @11
    @20
    @21
    @7
    cY
    c.pe
    fveq2
    sseq1d
    imbi12d
    sylan9bb
    spc2gv
    syl2anc
    mpid
    syl5
    mpd
end
