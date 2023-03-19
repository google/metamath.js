include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "cfv.mm"
include "cres.mm"
include "csumge0.mm"
include "wceq.mm"
include "jca.mm"
include "cdm.mm"
include "cpw.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "syl6sseq.mm"
include "cvv.mm"
include "wb.mm"
include "csalg.mm"
include "dmmeasal.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "cmea.mm"
include "ismea.mm"
include "sylib.mm"
include "simprd.mm"
include "breq1.mm"
include "disjeq1.mm"
include "anbi12d.mm"
include "unieq.mm"
include "fveq2d.mm"
include "reseq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem meadjuni
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cM: class M
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume meadjuni.m: |- ( ph -> M e. Meas )
  assume meadjuni.s: |- S = dom M
  assume meadjuni.x: |- ( ph -> X C_ S )
  assume meadjuni.cnb: |- ( ph -> X ~<_ _om )
  assume meadjuni.dj: |- ( ph -> Disj_ x e. X x )

  disjoint X x
  disjoint M y
  disjoint X y
  disjoint x y
  disjoint k x
  assert |- ( ph -> ( M ` U. X ) = ( sum^ ` ( M |` X ) ) )

  proof
    wph
    cX
    com
    cdom
    wbr
    #
    vx
    cX
    vx
    cv
    #
    wdisj
    #
    wa
    #
    cX
    cuni
    #
    cM
    cfv
    #
    cM
    cX
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    wph
    @0
    @2
    meadjuni.cnb
    meadjuni.dj
    jca
    wph
    cX
    cM
    cdm
    #
    cpw
    #
    wcel
    #
    vy
    cv
    #
    com
    cdom
    wbr
    #
    vx
    @12
    @1
    wdisj
    #
    wa
    #
    @12
    cuni
    #
    cM
    cfv
    #
    cM
    @12
    cres
    #
    csumge0
    cfv
    #
    wceq
    #
    wi
    #
    vy
    @10
    wral
    #
    @3
    @8
    wi
    #
    wph
    @11
    cX
    @9
    wss
    #
    wph
    cX
    cS
    @9
    meadjuni.x
    meadjuni.s
    syl6sseq
    wph
    cX
    cvv
    wcel
    @11
    @24
    wb
    wph
    cX
    cS
    csalg
    wph
    cS
    cM
    meadjuni.m
    meadjuni.s
    dmmeasal
    meadjuni.x
    ssexd
    cX
    @9
    cvv
    elpwg
    syl
    mpbird
    wph
    @9
    cc0
    cpnf
    cicc
    co
    cM
    wf
    @9
    csalg
    wcel
    wa
    c0
    cM
    cfv
    cc0
    wceq
    wa
    #
    @22
    wph
    cM
    cmea
    wcel
    @25
    @22
    wa
    meadjuni.m
    vy
    vx
    cM
    ismea
    sylib
    simprd
    @21
    @23
    vy
    cX
    @10
    @12
    cX
    wceq
    #
    @15
    @3
    @20
    @8
    @26
    @13
    @0
    @14
    @2
    @12
    cX
    com
    cdom
    breq1
    vx
    @12
    cX
    @1
    disjeq1
    anbi12d
    @26
    @17
    @5
    @19
    @7
    @26
    @16
    @4
    cM
    @12
    cX
    unieq
    fveq2d
    @26
    @18
    @6
    csumge0
    @12
    cX
    cM
    reseq2
    fveq2d
    eqeq12d
    imbi12d
    rspcva
    syl2anc
    mpd
end
