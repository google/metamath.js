include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "cfv.mm"
include "cres.mm"
include "csumge0.mm"
include "cle.mm"
include "cdm.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "elpwg.mm"
include "mpbird.mm"
include "wceq.mm"
include "omedm.mm"
include "pweqi.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "pweqd.mm"
include "eleqtrd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "c0.mm"
include "isome.mm"
include "mpbid.mm"
include "simprd.mm"
include "breq1.mm"
include "unieq.mm"
include "fveq2d.mm"
include "reseq2.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpd.mm"

theorem omeunile
  let wph: wff ph
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume omeunile.o: |- ( ph -> O e. OutMeas )
  assume omeunile.x: |- X = U. dom O
  assume omeunile.y: |- ( ph -> Y C_ ~P X )
  assume omeunile.ct: |- ( ph -> Y ~<_ _om )


  assert |- ( ph -> ( O ` U. Y ) <_ ( sum^ ` ( O |` Y ) ) )

  proof
    wph
    cY
    com
    cdom
    wbr
    #
    cY
    cuni
    #
    cO
    cfv
    #
    cO
    cY
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    omeunile.ct
    wph
    cY
    cO
    cdm
    #
    cpw
    #
    wcel
    vy
    cv
    #
    com
    cdom
    wbr
    #
    @8
    cuni
    #
    cO
    cfv
    #
    cO
    @8
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    @7
    wral
    #
    @0
    @5
    wi
    #
    wph
    cY
    cX
    cpw
    #
    cpw
    #
    @7
    wph
    cY
    @19
    wcel
    #
    cY
    @18
    wss
    #
    omeunile.y
    wph
    cY
    cvv
    wcel
    #
    @20
    @21
    wb
    wph
    @21
    @18
    cvv
    wcel
    #
    @22
    omeunile.y
    wph
    cX
    cvv
    wcel
    @23
    wph
    cO
    come
    cX
    omeunile.o
    omeunile.x
    unidmex
    cX
    cvv
    pwexg
    syl
    cY
    @18
    cvv
    ssexg
    syl2anc
    cY
    @18
    cvv
    elpwg
    syl
    mpbird
    wph
    @18
    @6
    wph
    @6
    @6
    cuni
    #
    cpw
    #
    @18
    wph
    cO
    come
    wcel
    #
    @6
    @25
    wceq
    #
    omeunile.o
    cO
    omedm
    syl
    @25
    @18
    wceq
    wph
    @18
    @25
    cX
    @24
    omeunile.x
    pweqi
    eqcomi
    a1i
    eqtr2d
    pweqd
    eleqtrd
    wph
    @6
    cc0
    cpnf
    cicc
    co
    cO
    wf
    @27
    wa
    c0
    cO
    cfv
    cc0
    wceq
    wa
    vx
    cv
    cO
    cfv
    @8
    cO
    cfv
    cle
    wbr
    vx
    @8
    cpw
    wral
    vy
    @25
    wral
    wa
    #
    @16
    wph
    @26
    @28
    @16
    wa
    #
    omeunile.o
    wph
    @26
    @26
    @29
    wb
    omeunile.o
    vy
    vx
    cO
    come
    isome
    syl
    mpbid
    simprd
    @15
    @17
    vy
    cY
    @7
    @8
    cY
    wceq
    #
    @9
    @0
    @14
    @5
    @8
    cY
    com
    cdom
    breq1
    @30
    @11
    @2
    @13
    @4
    cle
    @30
    @10
    @1
    cO
    @8
    cY
    unieq
    fveq2d
    @30
    @12
    @3
    csumge0
    @8
    cY
    cO
    reseq2
    fveq2d
    breq12d
    imbi12d
    rspcva
    syl2anc
    mpd
end
