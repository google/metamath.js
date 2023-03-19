include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "ccntz.mm"
include "wss.mm"
include "wa.mm"
include "cgrp.mm"
include "csubg.mm"
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
include "simpr.mm"
include "ralimi.mm"
include "syl.mm"
include "fveq2.mm"
include "sneq.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "fveq2d.mm"
include "ineq12d.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem dprddisj
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  let cZ: class Z
  assume dprdcntz.1: |- ( ph -> G dom DProd S )
  assume dprdcntz.2: |- ( ph -> dom S = I )
  assume dprdcntz.3: |- ( ph -> X e. I )
  assume dprddisj.0: |- .0. = ( 0g ` G )
  assume dprddisj.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( ph -> ( ( S ` X ) i^i ( K ` U. ( S " ( I \ { X } ) ) ) ) = { .0. } )

  proof
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
    cS
    cI
    @0
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    #
    vx
    cI
    wral
    #
    cX
    cS
    cfv
    #
    cS
    cI
    cX
    csn
    #
    cdif
    #
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    @8
    wceq
    #
    dprdcntz.3
    wph
    @1
    vy
    cv
    cS
    cfv
    cG
    ccntz
    cfv
    #
    cfv
    wss
    vy
    @3
    wral
    #
    @9
    wa
    #
    vx
    cI
    wral
    #
    @10
    wph
    cG
    cgrp
    wcel
    #
    cI
    cG
    csubg
    cfv
    cS
    wf
    #
    @22
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @23
    @24
    @22
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
    @25
    @26
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
    cK
    cvv
    c.0
    @19
    @19
    eqid
    dprddisj.0
    dprddisj.k
    dmdprd
    syl2anc
    mpbid
    simp3d
    @21
    @9
    vx
    cI
    @20
    @9
    simpr
    ralimi
    syl
    @9
    @18
    vx
    cX
    cI
    @0
    cX
    wceq
    #
    @7
    @17
    @8
    @27
    @1
    @11
    @6
    @16
    @0
    cX
    cS
    fveq2
    @27
    @5
    @15
    cK
    @27
    @4
    @14
    @27
    @3
    @13
    cS
    @27
    @2
    @12
    cI
    @0
    cX
    sneq
    difeq2d
    imaeq2d
    unieqd
    fveq2d
    ineq12d
    eqeq1d
    rspcv
    sylc
end
