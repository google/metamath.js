include "cn0.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cc.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "wss.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "sseldd.mm"
include "exp0d.mm"
include "cnfld1.mm"
include "subrg1cl.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cmul.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "expp1d.mm"
include "simp3.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "3exp.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem cnsrexpcl
  let wph: wff ph
  let cS: class S
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume cnsrexpcl.s: |- ( ph -> S e. ( SubRing ` CCfld ) )
  assume cnsrexpcl.x: |- ( ph -> X e. S )
  assume cnsrexpcl.y: |- ( ph -> Y e. NN0 )


  assert |- ( ph -> ( X ^ Y ) e. S )

  proof
    cY
    cn0
    wcel
    wph
    cX
    cY
    cexp
    co
    #
    cS
    wcel
    #
    cnsrexpcl.y
    wph
    cX
    va
    cv
    #
    cexp
    co
    #
    cS
    wcel
    #
    wi
    wph
    cX
    cc0
    cexp
    co
    #
    cS
    wcel
    #
    wi
    wph
    cX
    vb
    cv
    #
    cexp
    co
    #
    cS
    wcel
    #
    wi
    wph
    cX
    @7
    c1
    caddc
    co
    #
    cexp
    co
    #
    cS
    wcel
    #
    wi
    wph
    @1
    wi
    va
    vb
    cY
    @2
    cc0
    wceq
    #
    @4
    @6
    wph
    @13
    @3
    @5
    cS
    @2
    cc0
    cX
    cexp
    oveq2
    eleq1d
    imbi2d
    @2
    @7
    wceq
    #
    @4
    @9
    wph
    @14
    @3
    @8
    cS
    @2
    @7
    cX
    cexp
    oveq2
    eleq1d
    imbi2d
    @2
    @10
    wceq
    #
    @4
    @12
    wph
    @15
    @3
    @11
    cS
    @2
    @10
    cX
    cexp
    oveq2
    eleq1d
    imbi2d
    @2
    cY
    wceq
    #
    @4
    @1
    wph
    @16
    @3
    @0
    cS
    @2
    cY
    cX
    cexp
    oveq2
    eleq1d
    imbi2d
    wph
    @5
    c1
    cS
    wph
    cX
    wph
    cS
    cc
    cX
    wph
    cS
    ccnfld
    csubrg
    cfv
    wcel
    #
    cS
    cc
    wss
    cnsrexpcl.s
    cS
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    cnsrexpcl.x
    sseldd
    #
    exp0d
    wph
    @17
    c1
    cS
    wcel
    cnsrexpcl.s
    cS
    ccnfld
    c1
    cnfld1
    subrg1cl
    syl
    eqeltrd
    @7
    cn0
    wcel
    #
    wph
    @9
    @12
    @19
    wph
    @9
    @12
    @19
    wph
    @9
    w3a
    #
    @11
    @8
    cX
    cmul
    co
    #
    cS
    @20
    cX
    @7
    wph
    @19
    cX
    cc
    wcel
    @9
    @18
    3ad2ant2
    @19
    wph
    @9
    simp1
    expp1d
    @20
    @17
    @9
    cX
    cS
    wcel
    #
    @21
    cS
    wcel
    wph
    @19
    @17
    @9
    cnsrexpcl.s
    3ad2ant2
    @19
    wph
    @9
    simp3
    wph
    @19
    @22
    @9
    cnsrexpcl.x
    3ad2ant2
    cS
    ccnfld
    cmul
    @8
    cX
    cnfldmul
    subrgmcl
    syl3anc
    eqeltrd
    3exp
    a2d
    nn0ind
    mpcom
end
