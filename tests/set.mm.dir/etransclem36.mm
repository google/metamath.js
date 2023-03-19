include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cfa.mm"
include "cc0.mm"
include "cfz.mm"
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
include "cz.mm"
include "etransclem31.mm"
include "etransclem16.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cn0.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "etransclem11.mm"
include "3eqtri.mm"
include "simpr.mm"
include "etransclem26.mm"
include "fsumzcl.mm"
include "eqeltrd.mm"

theorem etransclem36
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
  let vd: setvar d
  let ve: setvar e
  let vk: setvar k
  let vm: setvar m
  assume etransclem36.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem36.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem36.p: |- ( ph -> P e. NN )
  assume etransclem36.m: |- ( ph -> M e. NN0 )
  assume etransclem36.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem36.n: |- ( ph -> N e. NN0 )
  assume etransclem36.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem36.jx: |- ( ph -> J e. X )
  assume etransclem36.jz: |- ( ph -> J e. ZZ )
  assume etransclem36.10: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )

  disjoint C c
  disjoint C j
  disjoint C n
  disjoint C x
  disjoint c j
  disjoint c n
  disjoint c x
  disjoint j n
  disjoint j x
  disjoint n x
  disjoint H c
  disjoint H j
  disjoint H n
  disjoint H x
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
  disjoint M d
  disjoint M e
  disjoint M k
  disjoint c d
  disjoint c e
  disjoint c k
  disjoint d e
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint e j
  disjoint e k
  disjoint e n
  disjoint j k
  disjoint k n
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint e m
  disjoint j m
  disjoint m n
  disjoint N e
  disjoint k x
  assert |- ( ph -> ( ( ( S Dn F ) ` N ) ` J ) e. ZZ )

  proof
    wph
    cJ
    cN
    cS
    cF
    cdvn
    co
    cfv
    cfv
    cN
    cC
    cfv
    #
    cN
    cfa
    cfv
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
    vj
    cprod
    cdiv
    co
    cP
    c1
    cmin
    co
    #
    cc0
    @3
    cfv
    #
    clt
    wbr
    cc0
    @5
    cfa
    cfv
    @5
    @6
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @7
    cexp
    co
    cmul
    co
    cif
    c1
    cM
    cfz
    co
    cP
    @4
    clt
    wbr
    cc0
    cP
    cfa
    cfv
    cP
    @4
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
    @8
    cexp
    co
    cmul
    co
    cif
    vj
    cprod
    cmul
    co
    cmul
    co
    #
    vc
    csu
    cz
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
    etransclem36.s
    etransclem36.x
    etransclem36.p
    etransclem36.m
    etransclem36.f
    etransclem36.n
    etransclem36.h
    etransclem36.10
    etransclem36.jx
    etransclem31
    wph
    @0
    @9
    vc
    wph
    cC
    vj
    vn
    cM
    cN
    vc
    etransclem36.10
    etransclem36.n
    etransclem16
    wph
    @3
    @0
    wcel
    #
    wa
    cC
    @3
    cP
    vj
    vn
    cJ
    cM
    cN
    ve
    wph
    cP
    cn
    wcel
    @10
    etransclem36.p
    adantr
    wph
    cM
    cn0
    wcel
    @10
    etransclem36.m
    adantr
    wph
    cN
    cn0
    wcel
    @10
    etransclem36.n
    adantr
    wph
    cJ
    cz
    wcel
    @10
    etransclem36.jz
    adantr
    cC
    vn
    cn0
    @1
    @4
    vj
    csu
    vn
    cv
    #
    wceq
    vc
    cc0
    @11
    cfz
    co
    @1
    cmap
    co
    #
    crab
    cmpt
    vm
    cn0
    @1
    vk
    cv
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
    @13
    cfz
    co
    @1
    cmap
    co
    crab
    cmpt
    vn
    cn0
    @1
    @2
    ve
    cv
    cfv
    vj
    csu
    @11
    wceq
    ve
    @12
    crab
    cmpt
    etransclem36.10
    vj
    vk
    vm
    vn
    cM
    vc
    vd
    etransclem11
    vk
    vj
    vn
    vm
    cM
    vd
    ve
    etransclem11
    3eqtri
    wph
    @10
    simpr
    etransclem26
    fsumzcl
    eqeltrd
end
