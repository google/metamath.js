include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "csu.mm"
include "cdvn.mm"
include "cdvds.mm"
include "etransclem16.mm"
include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nnzd.mm"
include "wa.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "etransclem12.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "rabid.mm"
include "biimpi.mm"
include "simprd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "nfcv.mm"
include "fzfid.mm"
include "cvv.mm"
include "wss.mm"
include "nn0ex.mm"
include "a1i.mm"
include "fzssnn0.mm"
include "mapss.mm"
include "sylancl.mm"
include "simpld.mm"
include "sseldd.mm"
include "mccl.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "wf.mm"
include "elmapi.mm"
include "3syl.mm"
include "cz.mm"
include "elfzelzd.mm"
include "etransclem10.mm"
include "caddc.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "sseli.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "eleq2s.mm"
include "adantl.mm"
include "etransclem3.mm"
include "fprodzcl.mm"
include "zmulcld.mm"
include "cmpt.mm"
include "etransclem11.mm"
include "eqtri.mm"
include "simpr.mm"
include "fveq2.mm"
include "cbvprodv.mm"
include "oveq2i.mm"
include "breq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "oveq12i.mm"
include "etransclem28.mm"
include "fsumdvds.mm"
include "etransclem31.mm"
include "breqtrrd.mm"

theorem etransclem37
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vd: setvar d
  assume etransclem37.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem37.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem37.p: |- ( ph -> P e. NN )
  assume etransclem37.m: |- ( ph -> M e. NN0 )
  assume etransclem37.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem37.n: |- ( ph -> N e. NN0 )
  assume etransclem37.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem37.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem37.9: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem37.j: |- ( ph -> J e. X )

  disjoint C c
  disjoint C j
  disjoint c j
  disjoint C x
  disjoint c x
  disjoint j x
  disjoint H c
  disjoint H j
  disjoint H n
  disjoint H x
  disjoint c n
  disjoint j n
  disjoint n x
  disjoint J c
  disjoint J j
  disjoint J x
  disjoint M c
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint N c
  disjoint N j
  disjoint N n
  disjoint N x
  disjoint P c
  disjoint P j
  disjoint P x
  disjoint S c
  disjoint S j
  disjoint S n
  disjoint S x
  disjoint X j
  disjoint X n
  disjoint X x
  disjoint c ph
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint C k
  disjoint C m
  disjoint c k
  disjoint c m
  disjoint j k
  disjoint j m
  disjoint k m
  disjoint J k
  disjoint M d
  disjoint M k
  disjoint M m
  disjoint c d
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint k n
  disjoint m n
  disjoint N d
  disjoint N k
  disjoint N m
  disjoint P k
  disjoint k ph
  disjoint m ph
  disjoint k x
  assert |- ( ph -> ( ! ` ( P - 1 ) ) || ( ( ( S Dn F ) ` N ) ` J ) )

  proof
    wph
    cP
    c1
    cmin
    co
    #
    cfa
    cfv
    #
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
    @0
    cc0
    @6
    cfv
    #
    clt
    wbr
    cc0
    @1
    @0
    @11
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @12
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
    @7
    clt
    wbr
    #
    cc0
    cP
    cfa
    cfv
    #
    cP
    @7
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cJ
    @5
    cmin
    co
    #
    @17
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    #
    vc
    csu
    cJ
    cN
    cS
    cF
    cdvn
    co
    cfv
    cfv
    cdvds
    wph
    @2
    @26
    vc
    @1
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem37.c
    etransclem37.n
    etransclem16
    wph
    @1
    wph
    @0
    wph
    cP
    cn
    wcel
    #
    @0
    cn0
    wcel
    etransclem37.p
    cP
    nnm1nn0
    syl
    faccld
    nnzd
    wph
    @6
    @2
    wcel
    #
    wa
    #
    @10
    @25
    @29
    @10
    @29
    @10
    @4
    @7
    vj
    csu
    #
    cfa
    cfv
    #
    @9
    cdiv
    co
    cn
    @29
    @3
    @31
    @9
    cdiv
    @29
    cN
    @30
    cfa
    @29
    @30
    cN
    @29
    @6
    @30
    cN
    wceq
    #
    vc
    cc0
    cN
    cfz
    co
    #
    @4
    cmap
    co
    #
    crab
    #
    wcel
    #
    @32
    wph
    @28
    @36
    wph
    @2
    @35
    @6
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem37.c
    etransclem37.n
    etransclem12
    eleq2d
    biimpa
    #
    @36
    @6
    @34
    wcel
    #
    @32
    @36
    @38
    @32
    wa
    @32
    vc
    @34
    rabid
    biimpi
    #
    simprd
    syl
    eqcomd
    fveq2d
    oveq1d
    @29
    @4
    @6
    vj
    vj
    @6
    nfcv
    @29
    cc0
    cM
    fzfid
    @29
    @36
    @6
    cn0
    @4
    cmap
    co
    #
    wcel
    @37
    @36
    @34
    @40
    @6
    @36
    cn0
    cvv
    wcel
    #
    @33
    cn0
    wss
    @34
    @40
    wss
    @41
    @36
    nn0ex
    a1i
    cN
    fzssnn0
    @33
    cn0
    @4
    cvv
    mapss
    sylancl
    @36
    @38
    @32
    @39
    simpld
    #
    sseldd
    syl
    mccl
    eqeltrd
    nnzd
    @29
    @13
    @24
    @29
    @6
    cP
    cJ
    cM
    cN
    wph
    @27
    @28
    etransclem37.p
    adantr
    #
    wph
    cM
    cn0
    wcel
    @28
    etransclem37.m
    adantr
    #
    @29
    @36
    @38
    @4
    @33
    @6
    wf
    #
    @37
    @42
    @6
    @33
    @4
    elmapi
    3syl
    #
    wph
    cJ
    cz
    wcel
    #
    @28
    wph
    cJ
    cc0
    cM
    etransclem37.9
    elfzelzd
    adantr
    #
    etransclem10
    @29
    @14
    @23
    vj
    @29
    c1
    cM
    fzfid
    @29
    @5
    @14
    wcel
    #
    wa
    @6
    cP
    @5
    cJ
    cM
    cN
    @29
    @27
    @49
    @43
    adantr
    @29
    @45
    @49
    @46
    adantr
    @49
    @5
    @4
    wcel
    #
    @29
    @50
    @5
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @14
    @52
    @4
    @5
    cc0
    cz
    wcel
    @52
    @4
    wss
    0z
    cc0
    cM
    fzp1ss
    ax-mp
    sseli
    c1
    @51
    cM
    cfz
    1e0p1
    oveq1i
    eleq2s
    adantl
    @29
    @47
    @49
    @48
    adantr
    etransclem3
    fprodzcl
    zmulcld
    zmulcld
    @29
    cC
    @6
    cP
    @26
    vk
    vm
    cJ
    cM
    cN
    vd
    @43
    @44
    wph
    cN
    cn0
    wcel
    @28
    etransclem37.n
    adantr
    cC
    vn
    cn0
    @30
    vn
    cv
    #
    wceq
    vc
    cc0
    @53
    cfz
    co
    @4
    cmap
    co
    crab
    cmpt
    vm
    cn0
    @4
    vk
    cv
    #
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @55
    cfz
    co
    @4
    cmap
    co
    crab
    cmpt
    etransclem37.c
    vj
    vk
    vm
    vn
    cM
    vc
    vd
    etransclem11
    eqtri
    wph
    @28
    simpr
    wph
    cJ
    @4
    wcel
    @28
    etransclem37.9
    adantr
    @10
    @3
    @4
    @54
    @6
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
    @25
    @13
    @14
    cP
    @56
    clt
    wbr
    #
    cc0
    @16
    cP
    @56
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cJ
    @54
    cmin
    co
    #
    @60
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vk
    cprod
    #
    cmul
    co
    cmul
    @9
    @58
    @3
    cdiv
    @4
    @8
    @57
    vj
    vk
    @5
    @54
    wceq
    #
    @7
    @56
    cfa
    @5
    @54
    @6
    fveq2
    #
    fveq2d
    cbvprodv
    oveq2i
    @24
    @67
    @13
    cmul
    @14
    @23
    @66
    vj
    vk
    @68
    @15
    @59
    @22
    @65
    cc0
    @68
    @7
    @56
    cP
    clt
    @69
    breq2d
    @68
    @19
    @62
    @21
    @64
    cmul
    @68
    @18
    @61
    @16
    cdiv
    @68
    @17
    @60
    cfa
    @68
    @7
    @56
    cP
    cmin
    @69
    oveq2d
    #
    fveq2d
    oveq2d
    @68
    @20
    @63
    @17
    @60
    cexp
    @5
    @54
    cJ
    cmin
    oveq2
    @70
    oveq12d
    oveq12d
    ifbieq2d
    cbvprodv
    oveq2i
    oveq12i
    etransclem28
    fsumdvds
    wph
    vx
    cC
    cP
    cS
    vj
    vn
    cF
    cH
    cM
    cN
    cX
    cJ
    vc
    etransclem37.s
    etransclem37.x
    etransclem37.p
    etransclem37.m
    etransclem37.f
    etransclem37.n
    etransclem37.h
    etransclem37.c
    etransclem37.j
    etransclem31
    breqtrrd
end
