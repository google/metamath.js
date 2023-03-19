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
include "dvdmsscn.mm"
include "etransclem4.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wss.mm"
include "adantr.mm"
include "cn.mm"
include "simpr.mm"
include "etransclem1.mm"
include "w3a.mm"
include "cr.mm"
include "cpr.mm"
include "3ad2ant1.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cmin.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "eqtri.mm"
include "simp2.mm"
include "cn0.mm"
include "elfznn0.mm"
include "3ad2ant3.mm"
include "etransclem20.mm"
include "dvnprod.mm"
include "eqtrd.mm"

theorem etransclem29
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vi: setvar i
  let vk: setvar k
  let vy: setvar y
  assume etranslemdvnf2lemlem.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem29.a: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem29.p: |- ( ph -> P e. NN )
  assume etransclem29.m: |- ( ph -> M e. NN0 )
  assume etransclem29.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem29.n: |- ( ph -> N e. NN0 )
  assume etransclem29.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem29.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )
  assume etransclem29.e: |- E = ( x e. X |-> prod_ j e. ( 0 ... M ) ( ( H ` j ) ` x ) )

  disjoint C c
  disjoint H c
  disjoint H j
  disjoint H n
  disjoint H x
  disjoint c j
  disjoint c n
  disjoint c x
  disjoint j n
  disjoint j x
  disjoint n x
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
  disjoint X x
  disjoint X n
  disjoint j ph
  disjoint ph x
  disjoint n ph
  disjoint H i
  disjoint i j
  disjoint i n
  disjoint i x
  disjoint M i
  disjoint M k
  disjoint M y
  disjoint i k
  disjoint i y
  disjoint j k
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint N i
  disjoint N k
  disjoint N y
  disjoint P k
  disjoint P y
  disjoint S i
  disjoint S y
  disjoint X i
  disjoint X k
  disjoint X y
  disjoint i ph
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( ( S Dn F ) ` N ) = ( x e. X |-> sum_ c e. ( C ` N ) ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( c ` j ) ) ) x. prod_ j e. ( 0 ... M ) ( ( ( S Dn ( H ` j ) ) ` ( c ` j ) ) ` x ) ) ) )

  proof
    wph
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    cN
    cS
    cE
    cdvn
    co
    #
    cfv
    vx
    cX
    cN
    cC
    cfv
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
    cfv
    #
    cfa
    cfv
    vj
    cprod
    cdiv
    co
    @2
    vx
    cv
    #
    @4
    cS
    @3
    cH
    cfv
    cdvn
    co
    cfv
    cfv
    vj
    cprod
    cmul
    co
    vc
    csu
    cmpt
    wph
    cN
    @0
    @1
    wph
    cF
    cE
    cS
    cdvn
    wph
    vx
    cX
    cP
    vj
    cE
    cF
    cH
    cM
    wph
    cS
    cX
    etranslemdvnf2lemlem.s
    etransclem29.a
    dvdmsscn
    #
    etransclem29.p
    etransclem29.m
    etransclem29.f
    etransclem29.h
    etransclem29.e
    etransclem4
    oveq2d
    fveq1d
    wph
    vx
    vj
    cC
    cS
    @2
    vi
    vn
    cE
    cH
    cN
    cX
    vc
    etranslemdvnf2lemlem.s
    etransclem29.a
    wph
    cc0
    cM
    fzfid
    wph
    @3
    @2
    wcel
    #
    wa
    vx
    cP
    vj
    cH
    @3
    cM
    cX
    wph
    cX
    cc
    wss
    @7
    @6
    adantr
    wph
    cP
    cn
    wcel
    #
    @7
    etransclem29.p
    adantr
    etransclem29.h
    wph
    @7
    simpr
    etransclem1
    etransclem29.n
    wph
    @7
    vi
    cv
    #
    cc0
    cN
    cfz
    co
    wcel
    #
    w3a
    vy
    cP
    cS
    vk
    cH
    @3
    cM
    @9
    cX
    wph
    @7
    cS
    cr
    cc
    cpr
    wcel
    @10
    etranslemdvnf2lemlem.s
    3ad2ant1
    wph
    @7
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @10
    etransclem29.a
    3ad2ant1
    wph
    @7
    @8
    @10
    etransclem29.p
    3ad2ant1
    cH
    vj
    @2
    vx
    cX
    @5
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
    vk
    @2
    vy
    cX
    vy
    cv
    vk
    cv
    #
    cmin
    co
    @12
    cc0
    wceq
    @11
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    etransclem29.h
    vx
    vy
    cP
    vj
    vk
    cM
    cX
    etransclem5
    eqtri
    wph
    @7
    @10
    simp2
    @10
    wph
    @9
    cn0
    wcel
    @7
    @9
    cN
    elfznn0
    3ad2ant3
    etransclem20
    etransclem29.e
    etransclem29.c
    dvnprod
    eqtrd
end
