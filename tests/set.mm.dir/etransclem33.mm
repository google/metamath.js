include "cc.mm"
include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "wf.mm"
include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cfa.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmin.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "cmul.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "wss.mm"
include "fzfi.mm"
include "mapfi.mm"
include "mp2an.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "faccld.mm"
include "nncnd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantllr.mm"
include "elfznn0.mm"
include "fprodcl.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "divcld.mm"
include "cr.mm"
include "cpr.mm"
include "ad3antrrr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cn.mm"
include "etransclem5.mm"
include "etransclem20.mm"
include "simpllr.mm"
include "ffvelrnd.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "etransclem11.mm"
include "etransclem30.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem etransclem33
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  assume etransclem33.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem33.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem33.p: |- ( ph -> P e. NN )
  assume etransclem33.m: |- ( ph -> M e. NN0 )
  assume etransclem33.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem33.n: |- ( ph -> N e. NN0 )

  disjoint M j
  disjoint M x
  disjoint j x
  disjoint N j
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S j
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint ph x
  disjoint M c
  disjoint M d
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint M w
  disjoint M z
  disjoint c w
  disjoint c z
  disjoint d w
  disjoint d z
  disjoint j w
  disjoint j z
  disjoint k w
  disjoint k z
  disjoint m w
  disjoint m z
  disjoint w z
  disjoint c x
  disjoint k x
  disjoint n x
  disjoint N c
  disjoint N d
  disjoint N m
  disjoint N n
  disjoint N w
  disjoint N z
  disjoint P c
  disjoint P k
  disjoint P n
  disjoint P y
  disjoint c y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint P w
  disjoint P z
  disjoint w x
  disjoint w y
  disjoint x z
  disjoint y z
  disjoint S c
  disjoint S n
  disjoint S z
  disjoint X c
  disjoint X k
  disjoint X n
  disjoint X y
  disjoint X w
  disjoint X z
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( S Dn F ) ` N ) : X --> CC )

  proof
    wph
    cX
    cc
    cN
    cS
    cF
    cdvn
    co
    cfv
    #
    wf
    cX
    cc
    vx
    cX
    cN
    vm
    cn0
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    vd
    cv
    cfv
    vk
    csu
    #
    vm
    cv
    #
    wceq
    #
    vd
    cc0
    @4
    cfz
    co
    #
    @1
    cmap
    co
    #
    crab
    #
    cmpt
    #
    cfv
    #
    cN
    cfa
    cfv
    #
    @1
    vj
    cv
    #
    vc
    cv
    #
    cfv
    #
    cfa
    cfv
    #
    vj
    cprod
    #
    cdiv
    co
    #
    @1
    vx
    cv
    #
    @14
    cS
    @12
    vk
    @1
    vy
    cX
    vy
    cv
    @2
    cmin
    co
    @2
    cc0
    wceq
    cP
    c1
    cmin
    co
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    #
    cfv
    cdvn
    co
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    cmul
    co
    #
    vc
    csu
    #
    cmpt
    #
    wf
    wph
    vx
    cX
    @24
    cc
    @25
    wph
    @18
    cX
    wcel
    #
    wa
    #
    @10
    @23
    vc
    wph
    @10
    cfn
    wcel
    @26
    wph
    @10
    @3
    cN
    wceq
    #
    vd
    cc0
    cN
    cfz
    co
    #
    @1
    cmap
    co
    #
    crab
    #
    cfn
    wph
    vm
    cN
    @8
    @31
    cn0
    @9
    cvv
    wph
    @9
    eqidd
    @4
    cN
    wceq
    #
    @8
    @31
    wceq
    wph
    @32
    @5
    @28
    vd
    @7
    @30
    @32
    @6
    @29
    @1
    cmap
    @4
    cN
    cc0
    cfz
    oveq2
    oveq1d
    @4
    cN
    @3
    eqeq2
    rabeqbidv
    adantl
    etransclem33.n
    @31
    cvv
    wcel
    wph
    @28
    vd
    @30
    @29
    @1
    cmap
    ovex
    rabex
    a1i
    fvmptd
    #
    @30
    cfn
    wcel
    #
    @31
    @30
    wss
    @31
    cfn
    wcel
    @29
    cfn
    wcel
    @1
    cfn
    wcel
    #
    @34
    cc0
    cN
    fzfi
    cc0
    cM
    fzfi
    #
    @29
    @1
    mapfi
    mp2an
    @28
    vd
    @30
    ssrab2
    #
    @30
    @31
    ssfi
    mp2an
    syl6eqel
    adantr
    @27
    @13
    @10
    wcel
    #
    wa
    #
    @17
    @22
    @39
    @11
    @16
    wph
    @11
    cc
    wcel
    @26
    @38
    wph
    @11
    wph
    cN
    etransclem33.n
    faccld
    nncnd
    ad2antrr
    @39
    @1
    @15
    vj
    @35
    @39
    @36
    a1i
    #
    @39
    @12
    @1
    wcel
    #
    wa
    #
    @15
    @42
    @14
    @42
    @14
    @29
    wcel
    #
    @14
    cn0
    wcel
    wph
    @38
    @41
    @43
    @26
    wph
    @38
    wa
    #
    @1
    @29
    @12
    @13
    @44
    @13
    @30
    wcel
    @1
    @29
    @13
    wf
    @44
    @31
    @30
    @13
    @37
    @44
    @13
    @10
    @31
    wph
    @38
    simpr
    wph
    @10
    @31
    wceq
    @38
    @33
    adantr
    eleqtrd
    sseldi
    @13
    @29
    @1
    elmapi
    syl
    ffvelrnda
    adantllr
    @14
    cN
    elfznn0
    syl
    #
    faccld
    #
    nncnd
    #
    fprodcl
    @39
    @1
    @15
    vj
    @40
    @47
    @42
    @15
    @46
    nnne0d
    fprodn0
    divcld
    @39
    @1
    @21
    vj
    @40
    @42
    cX
    cc
    @18
    @20
    @42
    vz
    cP
    cS
    vw
    @19
    @12
    cM
    @14
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    @26
    @38
    @41
    etransclem33.s
    ad3antrrr
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @26
    @38
    @41
    etransclem33.x
    ad3antrrr
    wph
    cP
    cn
    wcel
    @26
    @38
    @41
    etransclem33.p
    ad3antrrr
    vy
    vz
    cP
    vk
    vw
    cM
    cX
    etransclem5
    @39
    @41
    simpr
    @45
    etransclem20
    wph
    @26
    @38
    @41
    simpllr
    ffvelrnd
    fprodcl
    mulcld
    fsumcl
    @25
    eqid
    fmptd
    wph
    cX
    cc
    @0
    @25
    wph
    vx
    @9
    cP
    cS
    vj
    vn
    cF
    @19
    cM
    cN
    cX
    vc
    etransclem33.s
    etransclem33.x
    etransclem33.p
    etransclem33.m
    etransclem33.f
    etransclem33.n
    vy
    vx
    cP
    vk
    vj
    cM
    cX
    etransclem5
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    etransclem30
    feq1d
    mpbird
end
