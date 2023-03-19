include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "csu.mm"
include "ce.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "eftval.mm"
include "adantl.mm"
include "cr.mm"
include "reeftcl.mm"
include "sylan.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "reexpcl.mm"
include "wa.mm"
include "wbr.mm"
include "cmul.mm"
include "cn.mm"
include "faccl.mm"
include "nnred.mm"
include "adantr.mm"
include "simpr.mm"
include "expge0d.mm"
include "nnge1d.mm"
include "lemulge12d.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "cc.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "recnd.mm"
include "efcllem.mm"
include "syl.mm"
include "cabs.mm"
include "absidd.mm"
include "eqbrtrd.mm"
include "geolim.mm"
include "seqex.mm"
include "breldm.mm"
include "isumle.mm"
include "efval.mm"
include "expcl.mm"
include "isumclim.mm"
include "eqcomd.mm"
include "3brtr4d.mm"

theorem eflegeo
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  assume eflegeo.1: |- ( ph -> A e. RR )
  assume eflegeo.2: |- ( ph -> 0 <_ A )
  assume eflegeo.3: |- ( ph -> A < 1 )


  assert |- ( ph -> ( exp ` A ) <_ ( 1 / ( 1 - A ) ) )

  proof
    wph
    cn0
    cA
    vk
    cv
    #
    cexp
    co
    #
    @0
    cfa
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    cn0
    @1
    vk
    csu
    #
    cA
    ce
    cfv
    #
    c1
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cle
    wph
    @3
    @1
    vk
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    #
    @9
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    vn
    cn0
    @10
    cmpt
    #
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    @0
    cn0
    wcel
    #
    @0
    @11
    cfv
    @3
    wceq
    wph
    cA
    vn
    @11
    @0
    @11
    eqid
    #
    eftval
    adantl
    wph
    cA
    cr
    wcel
    #
    @14
    @3
    cr
    wcel
    eflegeo.1
    cA
    @0
    reeftcl
    sylan
    @14
    @0
    @12
    cfv
    @1
    wceq
    wph
    vn
    @0
    @10
    @1
    cn0
    @12
    @9
    @0
    cA
    cexp
    oveq2
    @12
    eqid
    cA
    @0
    cexp
    ovex
    fvmpt
    adantl
    #
    wph
    @16
    @14
    @1
    cr
    wcel
    #
    eflegeo.1
    cA
    @0
    reexpcl
    sylan
    #
    wph
    @14
    wa
    #
    @3
    @1
    cle
    wbr
    #
    @1
    @2
    @1
    cmul
    co
    cle
    wbr
    #
    @20
    @1
    @2
    @19
    @20
    @2
    @14
    @2
    cn
    wcel
    wph
    @0
    faccl
    adantl
    #
    nnred
    #
    @20
    cA
    @0
    wph
    @16
    @14
    eflegeo.1
    adantr
    wph
    @14
    simpr
    wph
    cc0
    cA
    cle
    wbr
    @14
    eflegeo.2
    adantr
    expge0d
    @20
    @2
    @23
    nnge1d
    lemulge12d
    @20
    @18
    @18
    @2
    cr
    wcel
    cc0
    @2
    clt
    wbr
    @21
    @22
    wb
    @19
    @19
    @24
    @20
    @2
    @23
    nngt0d
    @1
    @1
    @2
    ledivmul
    syl112anc
    mpbird
    wph
    cA
    cc
    wcel
    #
    caddc
    @11
    cc0
    cseq
    cli
    cdm
    #
    wcel
    wph
    cA
    eflegeo.1
    recnd
    #
    cA
    vn
    @11
    @15
    efcllem
    syl
    wph
    caddc
    @12
    cc0
    cseq
    #
    @8
    cli
    wbr
    @28
    @26
    wcel
    wph
    cA
    vk
    @12
    @27
    wph
    cA
    cabs
    cfv
    cA
    c1
    clt
    wph
    cA
    eflegeo.1
    eflegeo.2
    absidd
    eflegeo.3
    eqbrtrd
    @17
    geolim
    #
    @28
    @8
    cli
    caddc
    @12
    cc0
    seqex
    c1
    @7
    cdiv
    ovex
    breldm
    syl
    isumle
    wph
    @25
    @6
    @4
    wceq
    @27
    cA
    vk
    efval
    syl
    wph
    @5
    @8
    wph
    @1
    @8
    vk
    @12
    cc0
    cn0
    nn0uz
    @13
    @17
    wph
    @25
    @14
    @1
    cc
    wcel
    @27
    cA
    @0
    expcl
    sylan
    @29
    isumclim
    eqcomd
    3brtr4d
end
