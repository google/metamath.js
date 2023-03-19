include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cfa.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "etransclem30.mm"
include "dvdmsscn.mm"
include "etransclem16.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "adantr.mm"
include "faccld.mm"
include "nncnd.mm"
include "fzfid.mm"
include "cn0.mm"
include "fzssnn0.mm"
include "cmap.mm"
include "wf.mm"
include "wceq.mm"
include "crab.mm"
include "ssrab2.mm"
include "simpr.mm"
include "etransclem12.mm"
include "eleqtrd.mm"
include "sseldi.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "fprodcl.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "divcld.mm"
include "ssid.mm"
include "a1i.mm"
include "constcncfg.mm"
include "w3a.mm"
include "cr.mm"
include "cpr.mm"
include "ad2antrr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cn.mm"
include "cmin.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "eqtri.mm"
include "etransclem20.mm"
include "3adant2.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "feqmptd.mm"
include "etransclem22.mm"
include "eqeltrrd.mm"
include "fprodcncf.mm"
include "mulcncf.mm"
include "fsumcncf.mm"
include "eqeltrd.mm"

theorem etransclem34
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vj: setvar j
  let vy: setvar y
  assume etransclem34.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem34.a: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem34.p: |- ( ph -> P e. NN )
  assume etransclem34.m: |- ( ph -> M e. NN0 )
  assume etransclem34.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ k e. ( 1 ... M ) ( ( x - k ) ^ P ) ) )
  assume etransclem34.n: |- ( ph -> N e. NN0 )
  assume etransclem34.h: |- H = ( k e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - k ) ^ if ( k = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem34.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ k e. ( 0 ... M ) ( c ` k ) = n } )

  disjoint C c
  disjoint C k
  disjoint C x
  disjoint c k
  disjoint c x
  disjoint k x
  disjoint F c
  disjoint H c
  disjoint H k
  disjoint H n
  disjoint H x
  disjoint c n
  disjoint k n
  disjoint n x
  disjoint M c
  disjoint M k
  disjoint M x
  disjoint M n
  disjoint N c
  disjoint N k
  disjoint N x
  disjoint N n
  disjoint P k
  disjoint P x
  disjoint S c
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint X c
  disjoint X k
  disjoint X x
  disjoint X n
  disjoint c ph
  disjoint k ph
  disjoint ph x
  disjoint n ph
  disjoint k x
  disjoint C j
  disjoint C y
  disjoint c j
  disjoint c y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint M j
  disjoint M y
  disjoint N j
  disjoint N y
  disjoint P j
  disjoint P y
  disjoint S y
  disjoint X j
  disjoint X y
  disjoint j ph
  disjoint ph y
  assert |- ( ph -> ( ( S Dn F ) ` N ) e. ( X -cn-> CC ) )

  proof
    wph
    cN
    cS
    cF
    cdvn
    co
    cfv
    vx
    cX
    cN
    cC
    cfv
    #
    cN
    cfa
    cfv
    #
    cc0
    cM
    cfz
    co
    #
    vk
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
    vk
    cprod
    #
    cdiv
    co
    #
    @2
    vx
    cv
    #
    @5
    cS
    @3
    cH
    cfv
    cdvn
    co
    cfv
    #
    cfv
    #
    vk
    cprod
    #
    cmul
    co
    #
    vc
    csu
    cmpt
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cC
    cP
    cS
    vk
    vn
    cF
    cH
    cM
    cN
    cX
    vc
    etransclem34.s
    etransclem34.a
    etransclem34.p
    etransclem34.m
    etransclem34.f
    etransclem34.n
    etransclem34.h
    etransclem34.c
    etransclem30
    wph
    vx
    @0
    @13
    vc
    cX
    wph
    cS
    cX
    etransclem34.s
    etransclem34.a
    dvdmsscn
    #
    wph
    cC
    vk
    vn
    cM
    cN
    vc
    etransclem34.c
    etransclem34.n
    etransclem16
    wph
    @4
    @0
    wcel
    #
    wa
    #
    vx
    @8
    @12
    cX
    @17
    vx
    cX
    @8
    cc
    wph
    cX
    cc
    wss
    @16
    @15
    adantr
    #
    @17
    @1
    @7
    wph
    @1
    cc
    wcel
    @16
    wph
    @1
    wph
    cN
    etransclem34.n
    faccld
    nncnd
    adantr
    @17
    @2
    @6
    vk
    @17
    cc0
    cM
    fzfid
    #
    @17
    @3
    @2
    wcel
    #
    wa
    #
    @6
    @21
    @5
    @21
    cc0
    cN
    cfz
    co
    #
    cn0
    @5
    cN
    fzssnn0
    @17
    @2
    @22
    @3
    @4
    @17
    @4
    @22
    @2
    cmap
    co
    #
    wcel
    @2
    @22
    @4
    wf
    @17
    @2
    @5
    vk
    csu
    cN
    wceq
    #
    vc
    @23
    crab
    #
    @23
    @4
    @24
    vc
    @23
    ssrab2
    @17
    @4
    @0
    @25
    wph
    @16
    simpr
    wph
    @0
    @25
    wceq
    @16
    wph
    cC
    vk
    vn
    cM
    cN
    vc
    etransclem34.c
    etransclem34.n
    etransclem12
    adantr
    eleqtrd
    sseldi
    @4
    @22
    @2
    elmapi
    syl
    ffvelrnda
    sseldi
    #
    faccld
    #
    nncnd
    #
    fprodcl
    @17
    @2
    @6
    vk
    @19
    @28
    @21
    @6
    @27
    nnne0d
    fprodn0
    divcld
    cc
    cc
    wss
    @17
    cc
    ssid
    a1i
    constcncfg
    @17
    vx
    cX
    @2
    @11
    vk
    @18
    @19
    @17
    @9
    cX
    wcel
    #
    @20
    w3a
    cX
    cc
    @9
    @10
    @17
    @20
    cX
    cc
    @10
    wf
    @29
    @21
    vy
    cP
    cS
    vj
    cH
    @3
    cM
    @5
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    @16
    @20
    etransclem34.s
    ad2antrr
    #
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @16
    @20
    etransclem34.a
    ad2antrr
    #
    wph
    cP
    cn
    wcel
    @16
    @20
    etransclem34.p
    ad2antrr
    #
    cH
    vk
    @2
    vx
    cX
    @9
    @3
    cmin
    co
    @3
    cc0
    wceq
    cP
    c1
    cmin
    co
    #
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    vj
    @2
    vy
    cX
    vy
    cv
    vj
    cv
    #
    cmin
    co
    @34
    cc0
    wceq
    @33
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    etransclem34.h
    vx
    vy
    cP
    vk
    vj
    cM
    cX
    etransclem5
    eqtri
    #
    @17
    @20
    simpr
    #
    @26
    etransclem20
    #
    3adant2
    @17
    @29
    @20
    simp2
    ffvelrnd
    @21
    @10
    vx
    cX
    @11
    cmpt
    @14
    @21
    vx
    cX
    cc
    @10
    @37
    feqmptd
    @21
    vy
    cP
    cS
    vj
    cH
    @3
    cM
    @5
    cX
    @30
    @31
    @32
    @35
    @36
    @26
    etransclem22
    eqeltrrd
    fprodcncf
    mulcncf
    fsumcncf
    eqeltrd
end
