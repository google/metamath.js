include "cc.mm"
include "cdv.mm"
include "co.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "cmul.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt.mm"
include "cn.mm"
include "cmin.mm"
include "pserdv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "nn0uz.mm"
include "cuz.mm"
include "nnuz.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "1zzd.mm"
include "0zd.mm"
include "nncn.mm"
include "adantl.mm"
include "wf.mm"
include "adantr.mm"
include "nnnn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "mulcld.mm"
include "wss.mm"
include "cabs.mm"
include "ccnv.mm"
include "cico.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cr.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "a1i.mm"
include "sselda.mm"
include "nnm1nn0.mm"
include "expcl.mm"
include "isumshft.mm"
include "ax-1cn.mm"
include "nn0cn.mm"
include "addcom.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "pncan2.mm"
include "sumeq2dv.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem pserdv2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vr: setvar r
  let va: setvar a
  let vi: setvar i
  let vm: setvar m
  let vs: setvar s
  let vw: setvar w
  let vz: setvar z
  let vf: setvar f
  let cH: class H
  let vu: setvar u
  let vv: setvar v
  assume pserf.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume pserf.f: |- F = ( y e. S |-> sum_ j e. NN0 ( ( G ` y ) ` j ) )
  assume pserf.a: |- ( ph -> A : NN0 --> CC )
  assume pserf.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume psercn.s: |- S = ( `' abs " ( 0 [,) R ) )
  assume psercn.m: |- M = if ( R e. RR , ( ( ( abs ` a ) + R ) / 2 ) , ( ( abs ` a ) + 1 ) )
  assume pserdv.b: |- B = ( 0 ( ball ` ( abs o. - ) ) ( ( ( abs ` a ) + M ) / 2 ) )

  disjoint A n
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint M j
  disjoint M k
  disjoint M y
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint G j
  disjoint G k
  disjoint G r
  disjoint G y
  disjoint S a
  disjoint S j
  disjoint S k
  disjoint S y
  disjoint F a
  disjoint a ph
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint i n
  disjoint A i
  disjoint a m
  disjoint a s
  disjoint a w
  disjoint a z
  disjoint j m
  disjoint j s
  disjoint j w
  disjoint j z
  disjoint k m
  disjoint k s
  disjoint k w
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint r s
  disjoint r w
  disjoint r z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f i
  disjoint f j
  disjoint f y
  disjoint H f
  disjoint i j
  disjoint i y
  disjoint H i
  disjoint H j
  disjoint H y
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i z
  disjoint M i
  disjoint j u
  disjoint j v
  disjoint k u
  disjoint k v
  disjoint m u
  disjoint m v
  disjoint M m
  disjoint s u
  disjoint s v
  disjoint M s
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint i x
  disjoint B i
  disjoint B m
  disjoint B z
  disjoint i r
  disjoint G i
  disjoint G m
  disjoint G s
  disjoint G w
  disjoint G z
  disjoint a f
  disjoint a i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f z
  disjoint S f
  disjoint S i
  disjoint S m
  disjoint S w
  disjoint S z
  disjoint F f
  disjoint F z
  disjoint f ph
  disjoint i ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( ph -> ( CC _D F ) = ( y e. S |-> sum_ k e. NN ( ( k x. ( A ` k ) ) x. ( y ^ ( k - 1 ) ) ) ) )

  proof
    wph
    cc
    cF
    cdv
    co
    vy
    cS
    cn0
    vm
    cv
    #
    c1
    caddc
    co
    #
    @1
    cA
    cfv
    #
    cmul
    co
    #
    vy
    cv
    #
    @0
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    #
    cmpt
    vy
    cS
    cn
    vk
    cv
    #
    @8
    cA
    cfv
    #
    cmul
    co
    #
    @4
    @8
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    wph
    vx
    vy
    cA
    cB
    cR
    cS
    vj
    vm
    vn
    cF
    cG
    cM
    vr
    va
    pserf.g
    pserf.f
    pserf.a
    pserf.r
    psercn.s
    psercn.m
    pserdv.b
    pserdv
    wph
    vy
    cS
    @7
    @14
    wph
    @4
    cS
    wcel
    #
    wa
    #
    @14
    cn0
    c1
    @0
    caddc
    co
    #
    @17
    cA
    cfv
    #
    cmul
    co
    #
    @4
    @17
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    vm
    csu
    @7
    @16
    @13
    @22
    vk
    vm
    c1
    cc0
    cn
    cn0
    nn0uz
    cn
    c1
    cuz
    cfv
    cc0
    c1
    caddc
    co
    #
    cuz
    cfv
    nnuz
    c1
    @23
    cuz
    1e0p1
    fveq2i
    eqtri
    @8
    @17
    wceq
    #
    @10
    @19
    @12
    @21
    cmul
    @24
    @8
    @17
    @9
    @18
    cmul
    @24
    id
    @8
    @17
    cA
    fveq2
    oveq12d
    @24
    @11
    @20
    @4
    cexp
    @8
    @17
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    @16
    1zzd
    @16
    0zd
    @16
    @8
    cn
    wcel
    #
    wa
    #
    @10
    @12
    @26
    @8
    @9
    @25
    @8
    cc
    wcel
    @16
    @8
    nncn
    adantl
    @16
    cn0
    cc
    cA
    wf
    #
    @8
    cn0
    wcel
    @9
    cc
    wcel
    @25
    wph
    @27
    @15
    pserf.a
    adantr
    @8
    nnnn0
    cn0
    cc
    @8
    cA
    ffvelrn
    syl2an
    mulcld
    @16
    @4
    cc
    wcel
    @11
    cn0
    wcel
    @12
    cc
    wcel
    @25
    wph
    cS
    cc
    @4
    cS
    cc
    wss
    wph
    cS
    cabs
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    cc
    psercn.s
    @29
    cabs
    cdm
    cc
    cabs
    @28
    cnvimass
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    eqsstri
    a1i
    sselda
    @8
    nnm1nn0
    @4
    @11
    expcl
    syl2an
    mulcld
    isumshft
    @16
    cn0
    @22
    @6
    vm
    @16
    @0
    cn0
    wcel
    #
    wa
    #
    @19
    @3
    @21
    @5
    cmul
    @31
    @17
    @1
    @18
    @2
    cmul
    @31
    c1
    cc
    wcel
    #
    @0
    cc
    wcel
    #
    @17
    @1
    wceq
    ax-1cn
    @30
    @33
    @16
    @0
    nn0cn
    adantl
    #
    c1
    @0
    addcom
    sylancr
    #
    @31
    @17
    @1
    cA
    @35
    fveq2d
    oveq12d
    @31
    @20
    @0
    @4
    cexp
    @31
    @32
    @33
    @20
    @0
    wceq
    ax-1cn
    @34
    c1
    @0
    pncan2
    sylancr
    oveq2d
    oveq12d
    sumeq2dv
    eqtr2d
    mpteq2dva
    eqtrd
end
