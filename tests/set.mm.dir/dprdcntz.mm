include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "wne.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cima.mm"
include "cuni.mm"
include "csubg.mm"
include "cmrc.mm"
include "cin.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "cgrp.mm"
include "wf.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "dprddomcld.mm"
include "eqid.mm"
include "dmdprd.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp3d.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "fveq2d.mm"
include "sseq2d.mm"

theorem dprdcntz
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  assume dprdcntz.1: |- ( ph -> G dom DProd S )
  assume dprdcntz.2: |- ( ph -> dom S = I )
  assume dprdcntz.3: |- ( ph -> X e. I )
  assume dprdcntz.4: |- ( ph -> Y e. I )
  assume dprdcntz.5: |- ( ph -> X =/= Y )
  assume dprdcntz.z: |- Z = ( Cntz ` G )


  assert |- ( ph -> ( S ` X ) C_ ( Z ` ( S ` Y ) ) )

  proof
    wph
    cY
    cI
    cX
    csn
    #
    cdif
    #
    wcel
    #
    cX
    cS
    cfv
    #
    vy
    cv
    #
    cS
    cfv
    #
    cZ
    cfv
    #
    wss
    #
    vy
    @1
    wral
    #
    @3
    cY
    cS
    cfv
    #
    cZ
    cfv
    #
    wss
    #
    wph
    cY
    cI
    wcel
    cY
    cX
    wne
    @2
    dprdcntz.4
    wph
    cX
    cY
    dprdcntz.5
    necomd
    cY
    cI
    cX
    eldifsn
    sylanbrc
    wph
    cX
    cI
    wcel
    vx
    cv
    #
    cS
    cfv
    #
    @6
    wss
    #
    vy
    cI
    @12
    csn
    #
    cdif
    #
    wral
    #
    vx
    cI
    wral
    #
    @8
    dprdcntz.3
    wph
    @17
    @13
    cS
    @16
    cima
    cuni
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    cin
    cG
    c0g
    cfv
    #
    csn
    wceq
    #
    wa
    #
    vx
    cI
    wral
    #
    @18
    wph
    cG
    cgrp
    wcel
    #
    cI
    @19
    cS
    wf
    #
    @24
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @25
    @26
    @24
    w3a
    #
    dprdcntz.1
    wph
    cI
    cvv
    wcel
    cS
    cdm
    cI
    wceq
    @27
    @28
    wb
    wph
    cS
    cG
    cI
    dprdcntz.1
    dprdcntz.2
    dprddomcld
    dprdcntz.2
    vx
    vy
    cS
    cG
    cI
    @20
    cvv
    @21
    cZ
    dprdcntz.z
    @21
    eqid
    @20
    eqid
    dmdprd
    syl2anc
    mpbid
    simp3d
    @23
    @17
    vx
    cI
    @17
    @22
    simpl
    ralimi
    syl
    @17
    @8
    vx
    cX
    cI
    @12
    cX
    wceq
    #
    @14
    @7
    vy
    @16
    @1
    @29
    @15
    @0
    cI
    @12
    cX
    sneq
    difeq2d
    @29
    @13
    @3
    @6
    @12
    cX
    cS
    fveq2
    sseq1d
    raleqbidv
    rspcv
    sylc
    @7
    @11
    vy
    cY
    @1
    @4
    cY
    wceq
    #
    @6
    @10
    @3
    @30
    @5
    @9
    cZ
    @4
    cY
    cS
    fveq2
    fveq2d
    sseq2d
    rspcv
    sylc
end
