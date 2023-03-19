include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "cee.mm"
include "wcel.mm"
include "wb.mm"
include "ceeng.mm"
include "cbs.mm"
include "cn.mm"
include "eengbas.mm"
include "syl.mm"
include "syl6eqr.mm"
include "eleqtrrd.mm"
include "brcgr.mm"
include "syl22anc.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cds.mm"
include "dsid.mm"
include "fvexd.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "c7.mm"
include "cdc.mm"
include "cstr.mm"
include "eengstr.mm"
include "cle.mm"
include "w3a.mm"
include "cdm.mm"
include "wss.mm"
include "isstruct.mm"
include "simp2bi.mm"
include "structcnvcnv.mm"
include "funeqd.mm"
include "mpbird.mm"
include "cnx.mm"
include "cpr.mm"
include "citv.mm"
include "cbtwn.mm"
include "crab.mm"
include "clng.mm"
include "w3o.mm"
include "cun.mm"
include "opex.mm"
include "prid2.mm"
include "elun1.mm"
include "ax-mp.mm"
include "eengv.mm"
include "syl5eleqr.mm"
include "fvex.mm"
include "mpt2ex.mm"
include "a1i.mm"
include "strfv2d.mm"
include "syl6reqr.mm"
include "wa.mm"
include "simplrl.mm"
include "fveq1d.mm"
include "simplrr.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "sumex.mm"
include "ovmpt2d.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "bitrd.mm"

theorem ecgrtg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.mi: class .-
  let cN: class N
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ecgrtg.1: |- ( ph -> N e. NN )
  assume ecgrtg.2: |- P = ( Base ` ( EEG ` N ) )
  assume ecgrtg.3: |- .- = ( dist ` ( EEG ` N ) )
  assume ecgrtg.a: |- ( ph -> A e. P )
  assume ecgrtg.b: |- ( ph -> B e. P )
  assume ecgrtg.c: |- ( ph -> C e. P )
  assume ecgrtg.d: |- ( ph -> D e. P )


  assert |- ( ph -> ( <. A , B >. Cgr <. C , D >. <-> ( A .- B ) = ( C .- D ) ) )

  proof
    wph
    cA
    cB
    cop
    cC
    cD
    cop
    ccgr
    wbr
    #
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cA
    cfv
    #
    @2
    cB
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @1
    @2
    cC
    cfv
    #
    @2
    cD
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    wceq
    wph
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @16
    wcel
    cC
    @16
    wcel
    cD
    @16
    wcel
    @0
    @13
    wb
    wph
    cA
    cP
    @16
    ecgrtg.a
    wph
    @16
    cN
    ceeng
    cfv
    #
    cbs
    cfv
    #
    cP
    wph
    cN
    cn
    wcel
    #
    @16
    @18
    wceq
    ecgrtg.1
    cN
    eengbas
    syl
    ecgrtg.2
    syl6eqr
    #
    eleqtrrd
    #
    wph
    cB
    cP
    @16
    ecgrtg.b
    @20
    eleqtrrd
    #
    wph
    cC
    cP
    @16
    ecgrtg.c
    @20
    eleqtrrd
    #
    wph
    cD
    cP
    @16
    ecgrtg.d
    @20
    eleqtrrd
    #
    cA
    cB
    cC
    cD
    vi
    cN
    brcgr
    syl22anc
    wph
    @7
    @14
    @12
    @15
    wph
    @14
    @7
    wph
    vx
    vy
    cA
    cB
    @16
    @16
    @1
    @2
    vx
    cv
    #
    cfv
    #
    @2
    vy
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @7
    c.mi
    cvv
    wph
    vx
    vy
    @16
    @16
    @31
    cmpt2
    #
    @17
    cds
    cfv
    c.mi
    wph
    @32
    @17
    cds
    cvv
    cvv
    dsid
    wph
    cN
    ceeng
    fvexd
    wph
    @17
    ccnv
    ccnv
    #
    wfun
    @17
    c0
    csn
    cdif
    #
    wfun
    #
    wph
    @17
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
    @35
    wph
    @19
    @38
    ecgrtg.1
    cN
    eengstr
    syl
    #
    @38
    c1
    cn
    wcel
    @36
    cn
    wcel
    c1
    @36
    cle
    wbr
    w3a
    @35
    @17
    cdm
    c1
    @36
    cfz
    co
    wss
    @17
    c1
    @36
    isstruct
    simp2bi
    syl
    wph
    @33
    @34
    wph
    @38
    @33
    @34
    wceq
    @39
    @17
    @37
    structcnvcnv
    syl
    funeqd
    mpbird
    wph
    cnx
    cds
    cfv
    #
    @32
    cop
    #
    cnx
    cbs
    cfv
    @16
    cop
    #
    @41
    cpr
    #
    cnx
    citv
    cfv
    vx
    vy
    @16
    @16
    vz
    cv
    #
    @25
    @27
    cop
    cbtwn
    wbr
    #
    vz
    @16
    crab
    cmpt2
    cop
    cnx
    clng
    cfv
    vx
    vy
    @16
    @16
    @25
    csn
    cdif
    @45
    @25
    @44
    @27
    cop
    cbtwn
    wbr
    @27
    @25
    @44
    cop
    cbtwn
    wbr
    w3o
    vz
    @16
    crab
    cmpt2
    cop
    cpr
    #
    cun
    #
    @17
    @41
    @43
    wcel
    @41
    @47
    wcel
    @42
    @41
    @40
    @32
    opex
    prid2
    @41
    @43
    @46
    elun1
    ax-mp
    wph
    @19
    @17
    @47
    wceq
    ecgrtg.1
    vx
    vy
    vz
    vi
    cN
    eengv
    syl
    syl5eleqr
    @32
    cvv
    wcel
    wph
    vx
    vy
    @16
    @16
    @31
    cN
    cee
    fvex
    #
    @48
    mpt2ex
    a1i
    strfv2d
    ecgrtg.3
    syl6reqr
    #
    wph
    @25
    cA
    wceq
    #
    @27
    cB
    wceq
    #
    wa
    wa
    #
    @1
    @30
    @6
    vi
    @52
    @2
    @1
    wcel
    #
    wa
    #
    @29
    @5
    c2
    cexp
    @54
    @26
    @3
    @28
    @4
    cmin
    @54
    @2
    @25
    cA
    wph
    @50
    @51
    @53
    simplrl
    fveq1d
    @54
    @2
    @27
    cB
    wph
    @50
    @51
    @53
    simplrr
    fveq1d
    oveq12d
    oveq1d
    sumeq2dv
    @21
    @22
    @7
    cvv
    wcel
    wph
    @1
    @6
    vi
    sumex
    a1i
    ovmpt2d
    eqcomd
    wph
    @15
    @12
    wph
    vx
    vy
    cC
    cD
    @16
    @16
    @31
    @12
    c.mi
    cvv
    @49
    wph
    @25
    cC
    wceq
    #
    @27
    cD
    wceq
    #
    wa
    wa
    #
    @1
    @30
    @11
    vi
    @57
    @53
    wa
    #
    @29
    @10
    c2
    cexp
    @58
    @26
    @8
    @28
    @9
    cmin
    @58
    @2
    @25
    cC
    wph
    @55
    @56
    @53
    simplrl
    fveq1d
    @58
    @2
    @27
    cD
    wph
    @55
    @56
    @53
    simplrr
    fveq1d
    oveq12d
    oveq1d
    sumeq2dv
    @23
    @24
    @12
    cvv
    wcel
    wph
    @1
    @11
    vi
    sumex
    a1i
    ovmpt2d
    eqcomd
    eqeq12d
    bitrd
end
