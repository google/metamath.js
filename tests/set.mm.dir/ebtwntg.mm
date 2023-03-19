include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cee.mm"
include "cfv.mm"
include "crab.mm"
include "cvv.mm"
include "cmpt2.mm"
include "ceeng.mm"
include "citv.mm"
include "itvid.mm"
include "fvexd.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c1.mm"
include "c7.mm"
include "cdc.mm"
include "cstr.mm"
include "cn.mm"
include "eengstr.mm"
include "syl.mm"
include "cle.mm"
include "w3a.mm"
include "cdm.mm"
include "cfz.mm"
include "wss.mm"
include "isstruct.mm"
include "simp2bi.mm"
include "wceq.mm"
include "structcnvcnv.mm"
include "funeqd.mm"
include "mpbird.mm"
include "cnx.mm"
include "cbs.mm"
include "cds.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cpr.mm"
include "clng.mm"
include "w3o.mm"
include "cun.mm"
include "opex.mm"
include "prid1.mm"
include "elun2.mm"
include "ax-mp.mm"
include "eengv.mm"
include "syl5eleqr.mm"
include "fvex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "strfv2d.mm"
include "syl6reqr.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "opeq12d.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "syl6eleq.mm"
include "eengbas.mm"
include "eleqtrrd.mm"
include "rabex.mm"
include "ovmpt2d.mm"
include "eleq2d.mm"
include "wb.mm"
include "breq1.mm"
include "elrab3.mm"
include "bitr2d.mm"

theorem ebtwntg
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ebtwntg.1: |- ( ph -> N e. NN )
  assume ebtwntg.2: |- P = ( Base ` ( EEG ` N ) )
  assume ebtwntg.3: |- I = ( Itv ` ( EEG ` N ) )
  assume ebtwntg.x: |- ( ph -> X e. P )
  assume ebtwntg.y: |- ( ph -> Y e. P )
  assume ebtwntg.z: |- ( ph -> Z e. P )


  assert |- ( ph -> ( Z Btwn <. X , Y >. <-> Z e. ( X I Y ) ) )

  proof
    wph
    cZ
    cX
    cY
    cI
    co
    #
    wcel
    cZ
    vz
    cv
    #
    cX
    cY
    cop
    #
    cbtwn
    wbr
    #
    vz
    cN
    cee
    cfv
    #
    crab
    #
    wcel
    #
    cZ
    @2
    cbtwn
    wbr
    #
    wph
    @0
    @5
    cZ
    wph
    vx
    vy
    cX
    cY
    @4
    @4
    @1
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vz
    @4
    crab
    #
    @5
    cI
    cvv
    wph
    vx
    vy
    @4
    @4
    @12
    cmpt2
    #
    cN
    ceeng
    cfv
    #
    citv
    cfv
    cI
    wph
    @13
    @14
    citv
    cvv
    cvv
    itvid
    wph
    cN
    ceeng
    fvexd
    wph
    @14
    ccnv
    ccnv
    #
    wfun
    @14
    c0
    csn
    cdif
    #
    wfun
    #
    wph
    @14
    c1
    c1
    c7
    cdc
    #
    cop
    #
    cstr
    wbr
    #
    @17
    wph
    cN
    cn
    wcel
    #
    @20
    ebtwntg.1
    cN
    eengstr
    syl
    #
    @20
    c1
    cn
    wcel
    @18
    cn
    wcel
    c1
    @18
    cle
    wbr
    w3a
    @17
    @14
    cdm
    c1
    @18
    cfz
    co
    wss
    @14
    c1
    @18
    isstruct
    simp2bi
    syl
    wph
    @15
    @16
    wph
    @20
    @15
    @16
    wceq
    @22
    @14
    @19
    structcnvcnv
    syl
    funeqd
    mpbird
    wph
    cnx
    citv
    cfv
    #
    @13
    cop
    #
    cnx
    cbs
    cfv
    @4
    cop
    cnx
    cds
    cfv
    vx
    vy
    @4
    @4
    c1
    cN
    cfz
    co
    vi
    cv
    #
    @8
    cfv
    @25
    @9
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    cmpt2
    cop
    cpr
    #
    @24
    cnx
    clng
    cfv
    vx
    vy
    @4
    @4
    @8
    csn
    cdif
    @11
    @8
    @1
    @9
    cop
    cbtwn
    wbr
    @9
    @8
    @1
    cop
    cbtwn
    wbr
    w3o
    vz
    @4
    crab
    cmpt2
    cop
    #
    cpr
    #
    cun
    #
    @14
    @24
    @28
    wcel
    @24
    @29
    wcel
    @24
    @27
    @23
    @13
    opex
    prid1
    @24
    @28
    @26
    elun2
    ax-mp
    wph
    @21
    @14
    @29
    wceq
    ebtwntg.1
    vx
    vy
    vz
    vi
    cN
    eengv
    syl
    syl5eleqr
    @13
    cvv
    wcel
    wph
    vx
    vy
    @4
    @4
    @12
    cN
    cee
    fvex
    #
    @30
    mpt2ex
    a1i
    strfv2d
    ebtwntg.3
    syl6reqr
    wph
    @8
    cX
    wceq
    #
    @9
    cY
    wceq
    #
    wa
    wa
    #
    @11
    @3
    vz
    @4
    @33
    @10
    @2
    @1
    cbtwn
    @33
    @8
    cX
    @9
    cY
    wph
    @31
    @32
    simprl
    wph
    @31
    @32
    simprr
    opeq12d
    breq2d
    rabbidv
    wph
    cX
    @14
    cbs
    cfv
    #
    @4
    wph
    cX
    cP
    @34
    ebtwntg.x
    ebtwntg.2
    syl6eleq
    wph
    @21
    @4
    @34
    wceq
    ebtwntg.1
    cN
    eengbas
    syl
    #
    eleqtrrd
    wph
    cY
    @34
    @4
    wph
    cY
    cP
    @34
    ebtwntg.y
    ebtwntg.2
    syl6eleq
    @35
    eleqtrrd
    @5
    cvv
    wcel
    wph
    @3
    vz
    @4
    @30
    rabex
    a1i
    ovmpt2d
    eleq2d
    wph
    cZ
    @4
    wcel
    @6
    @7
    wb
    wph
    cZ
    @34
    @4
    wph
    cZ
    cP
    @34
    ebtwntg.z
    ebtwntg.2
    syl6eleq
    @35
    eleqtrrd
    @3
    @7
    vz
    cZ
    @4
    @1
    cZ
    @2
    cbtwn
    breq1
    elrab3
    syl
    bitr2d
end
