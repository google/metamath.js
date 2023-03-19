include "cfa.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "csu.mm"
include "cn.mm"
include "cmap.mm"
include "wcel.mm"
include "wceq.mm"
include "crab.mm"
include "wa.mm"
include "etransclem12.mm"
include "eleqtrd.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "nfcv.mm"
include "fzfid.mm"
include "cn0.mm"
include "cvv.mm"
include "wss.mm"
include "nn0ex.mm"
include "fzssnn0.mm"
include "mapss.mm"
include "mp2an.mm"
include "simpld.mm"
include "sseldi.mm"
include "mccl.mm"
include "eqeltrd.mm"
include "nnzd.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "etransclem10.mm"
include "adantr.mm"
include "caddc.mm"
include "cz.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "etransclem3.mm"
include "fprodzcl.mm"
include "zmulcld.mm"

theorem etransclem26
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cP: class P
  let vj: setvar j
  let vn: setvar n
  let cJ: class J
  let cM: class M
  let cN: class N
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume etransclem26.p: |- ( ph -> P e. NN )
  assume etransclem26.m: |- ( ph -> M e. NN0 )
  assume etransclem26.n: |- ( ph -> N e. NN0 )
  assume etransclem26.jz: |- ( ph -> J e. ZZ )
  assume etransclem26.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem26.d: |- ( ph -> D e. ( C ` N ) )

  disjoint D c
  disjoint D j
  disjoint c j
  disjoint M c
  disjoint M j
  disjoint M n
  disjoint c n
  disjoint j n
  disjoint N c
  disjoint N n
  disjoint j ph
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( D ` j ) ) ) x. ( if ( ( P - 1 ) < ( D ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( D ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( D ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( D ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( D ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( D ` j ) ) ) ) ) ) ) e. ZZ )

  proof
    wph
    cN
    cfa
    cfv
    #
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    cD
    cfv
    #
    cfa
    cfv
    vj
    cprod
    #
    cdiv
    co
    #
    cP
    c1
    cmin
    co
    #
    cc0
    cD
    cfv
    #
    clt
    wbr
    cc0
    @6
    cfa
    cfv
    @6
    @7
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @8
    cexp
    co
    cmul
    co
    cif
    #
    c1
    cM
    cfz
    co
    #
    cP
    @3
    clt
    wbr
    cc0
    cP
    cfa
    cfv
    cP
    @3
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @2
    cmin
    co
    @11
    cexp
    co
    cmul
    co
    cif
    #
    vj
    cprod
    #
    cmul
    co
    wph
    @5
    wph
    @5
    @1
    @3
    vj
    csu
    #
    cfa
    cfv
    #
    @4
    cdiv
    co
    cn
    wph
    @0
    @15
    @4
    cdiv
    wph
    cN
    @14
    cfa
    wph
    @14
    cN
    wph
    cD
    cc0
    cN
    cfz
    co
    #
    @1
    cmap
    co
    #
    wcel
    #
    @14
    cN
    wceq
    #
    wph
    cD
    @1
    @2
    vc
    cv
    #
    cfv
    #
    vj
    csu
    #
    cN
    wceq
    #
    vc
    @17
    crab
    #
    wcel
    @18
    @19
    wa
    wph
    cD
    cN
    cC
    cfv
    @24
    etransclem26.d
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem26.c
    etransclem26.n
    etransclem12
    eleqtrd
    @23
    @19
    vc
    cD
    @17
    @20
    cD
    wceq
    #
    @22
    @14
    cN
    @25
    @1
    @21
    @3
    vj
    @2
    @20
    cD
    fveq1
    sumeq2ad
    eqeq1d
    elrab
    sylib
    #
    simprd
    eqcomd
    fveq2d
    oveq1d
    wph
    @1
    cD
    vj
    vj
    cD
    nfcv
    wph
    cc0
    cM
    fzfid
    wph
    @17
    cn0
    @1
    cmap
    co
    #
    cD
    cn0
    cvv
    wcel
    @16
    cn0
    wss
    @17
    @27
    wss
    nn0ex
    cN
    fzssnn0
    @16
    cn0
    @1
    cvv
    mapss
    mp2an
    wph
    @18
    @19
    @26
    simpld
    #
    sseldi
    mccl
    eqeltrd
    nnzd
    wph
    @9
    @13
    wph
    cD
    cP
    cJ
    cM
    cN
    etransclem26.p
    etransclem26.m
    wph
    @18
    @1
    @16
    cD
    wf
    #
    @28
    cD
    @16
    @1
    elmapi
    syl
    #
    etransclem26.jz
    etransclem10
    wph
    @10
    @12
    vj
    wph
    c1
    cM
    fzfid
    wph
    @2
    @10
    wcel
    #
    wa
    cD
    cP
    @2
    cJ
    cM
    cN
    wph
    cP
    cn
    wcel
    @31
    etransclem26.p
    adantr
    wph
    @29
    @31
    @30
    adantr
    @31
    @2
    @1
    wcel
    wph
    @31
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @1
    @2
    cc0
    cz
    wcel
    @33
    @1
    wss
    0z
    cc0
    cM
    fzp1ss
    ax-mp
    @31
    @2
    @33
    wcel
    @10
    @33
    @2
    c1
    @32
    cM
    cfz
    1e0p1
    oveq1i
    eleq2i
    biimpi
    sseldi
    adantl
    wph
    cJ
    cz
    wcel
    @31
    etransclem26.jz
    adantr
    etransclem3
    fprodzcl
    zmulcld
    zmulcld
end
