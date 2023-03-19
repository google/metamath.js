include "csubg.mm"
include "cfv.mm"
include "cmrc.mm"
include "cvv.mm"
include "eqid.mm"
include "cres.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cgrp.mm"
include "wcel.mm"
include "dprdgrp.mm"
include "syl.mm"
include "cun.mm"
include "wf.mm"
include "wceq.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "fssresd.mm"
include "fdm.mm"
include "dprddomcld.mm"
include "ssun2.mm"
include "unexg.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "cv.mm"
include "wne.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "dmdprdsplit2lem.mm"
include "c0.mm"
include "incom.mm"
include "syl5eqr.mm"
include "uncom.mm"
include "syl6eq.mm"
include "co.mm"
include "dprdsubg.mm"
include "cntzrecd.mm"
include "jaodan.mm"
include "simpld.mm"
include "ex.mm"
include "sylbid.mm"
include "3imp2.mm"
include "biimpa.mm"
include "simprd.mm"
include "syldan.mm"
include "dmdprdd.mm"

theorem dmdprdsplit2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let cZ: class Z
  let c.po: class .(+)
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume dprdsplit.2: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dprdsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprdsplit.u: |- ( ph -> I = ( C u. D ) )
  assume dmdprdsplit.z: |- Z = ( Cntz ` G )
  assume dmdprdsplit.0: |- .0. = ( 0g ` G )
  assume dmdprdsplit2.1: |- ( ph -> G dom DProd ( S |` C ) )
  assume dmdprdsplit2.2: |- ( ph -> G dom DProd ( S |` D ) )
  assume dmdprdsplit2.3: |- ( ph -> ( G DProd ( S |` C ) ) C_ ( Z ` ( G DProd ( S |` D ) ) ) )
  assume dmdprdsplit2.4: |- ( ph -> ( ( G DProd ( S |` C ) ) i^i ( G DProd ( S |` D ) ) ) = { .0. } )


  assert |- ( ph -> G dom DProd S )

  proof
    wph
    vx
    vy
    cS
    cG
    cI
    cG
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cvv
    c.0
    cZ
    dmdprdsplit.z
    dmdprdsplit.0
    @1
    eqid
    #
    wph
    cG
    cS
    cC
    cres
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    cgrp
    wcel
    dmdprdsplit2.1
    @3
    cG
    dprdgrp
    syl
    wph
    cI
    cC
    cD
    cun
    #
    cvv
    dprdsplit.u
    wph
    cC
    cvv
    wcel
    cD
    cvv
    wcel
    @6
    cvv
    wcel
    wph
    @3
    cG
    cC
    dmdprdsplit2.1
    wph
    cC
    @0
    @3
    wf
    @3
    cdm
    cC
    wceq
    wph
    cI
    @0
    cC
    cS
    dprdsplit.2
    wph
    @6
    cC
    cI
    cC
    cD
    ssun1
    dprdsplit.u
    syl5sseqr
    fssresd
    cC
    @0
    @3
    fdm
    syl
    dprddomcld
    wph
    cS
    cD
    cres
    #
    cG
    cD
    dmdprdsplit2.2
    wph
    cD
    @0
    @7
    wf
    @7
    cdm
    cD
    wceq
    wph
    cI
    @0
    cD
    cS
    dprdsplit.2
    wph
    @6
    cD
    cI
    cD
    cC
    ssun2
    dprdsplit.u
    syl5sseqr
    fssresd
    cD
    @0
    @7
    fdm
    syl
    dprddomcld
    cC
    cD
    cvv
    cvv
    unexg
    syl2anc
    eqeltrd
    dprdsplit.2
    wph
    vx
    cv
    #
    cI
    wcel
    #
    vy
    cv
    #
    cI
    wcel
    #
    @8
    @10
    wne
    #
    @8
    cS
    cfv
    #
    @10
    cS
    cfv
    cZ
    cfv
    wss
    #
    wph
    @9
    @8
    cC
    wcel
    #
    @8
    cD
    wcel
    #
    wo
    #
    @11
    @12
    @14
    wi
    wi
    #
    wph
    @9
    @8
    @6
    wcel
    @17
    wph
    cI
    @6
    @8
    dprdsplit.u
    eleq2d
    @8
    cC
    cD
    elun
    syl6bb
    #
    wph
    @17
    @18
    wph
    @17
    wa
    @18
    @13
    cS
    cI
    @8
    csn
    cdif
    cima
    cuni
    @1
    cfv
    cin
    c.0
    csn
    #
    wss
    #
    wph
    @15
    @18
    @21
    wa
    @16
    wph
    cC
    cD
    cS
    cG
    cI
    @1
    @8
    @10
    c.0
    cZ
    dprdsplit.2
    dprdsplit.i
    dprdsplit.u
    dmdprdsplit.z
    dmdprdsplit.0
    dmdprdsplit2.1
    dmdprdsplit2.2
    dmdprdsplit2.3
    dmdprdsplit2.4
    @2
    dmdprdsplit2lem
    #
    wph
    cD
    cC
    cS
    cG
    cI
    @1
    @8
    @10
    c.0
    cZ
    dprdsplit.2
    wph
    cD
    cC
    cin
    cC
    cD
    cin
    c0
    cC
    cD
    incom
    dprdsplit.i
    syl5eqr
    wph
    cI
    @6
    cD
    cC
    cun
    dprdsplit.u
    cC
    cD
    uncom
    syl6eq
    dmdprdsplit.z
    dmdprdsplit.0
    dmdprdsplit2.2
    dmdprdsplit2.1
    wph
    cG
    @3
    cdprd
    co
    #
    cG
    @7
    cdprd
    co
    #
    cG
    cZ
    dmdprdsplit.z
    wph
    @5
    @23
    @0
    wcel
    dmdprdsplit2.1
    @3
    cG
    dprdsubg
    syl
    wph
    cG
    @7
    @4
    wbr
    @24
    @0
    wcel
    dmdprdsplit2.2
    @7
    cG
    dprdsubg
    syl
    dmdprdsplit2.3
    cntzrecd
    wph
    @24
    @23
    cin
    @23
    @24
    cin
    @20
    @23
    @24
    incom
    dmdprdsplit2.4
    syl5eqr
    @2
    dmdprdsplit2lem
    #
    jaodan
    simpld
    ex
    sylbid
    3imp2
    wph
    @9
    @17
    @21
    wph
    @9
    @17
    @19
    biimpa
    wph
    @15
    @21
    @16
    wph
    @15
    wa
    @18
    @21
    @22
    simprd
    wph
    @16
    wa
    @18
    @21
    @25
    simprd
    jaodan
    syldan
    dmdprdd
end
