include "cn.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "ceu.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "caddc.mm"
include "cfl.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cn0.mm"
include "nnnn0.mm"
include "subfacf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "nn0zd.mm"
include "zred.mm"
include "cr.mm"
include "crp.mm"
include "faccl.mm"
include "nnred.mm"
include "epr.mm"
include "rerpdivcl.mm"
include "sylancl.mm"
include "halfre.mm"
include "readdcl.mm"
include "cmin.mm"
include "cabs.mm"
include "wa.mm"
include "cuz.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "cc0.mm"
include "fveq2.mm"
include "fac1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "subfac1.mm"
include "oveq12d.mm"
include "rpreccl.mm"
include "ax-mp.mm"
include "rpre.mm"
include "recni.mm"
include "subid1i.mm"
include "fveq2d.mm"
include "rpge0.mm"
include "absid.mm"
include "mp2an.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "2re.mm"
include "ere.mm"
include "2pos.mm"
include "epos.mm"
include "ltrecii.mm"
include "mpbi.mm"
include "syl6eqbr.mm"
include "cc.mm"
include "eluz2nn.mm"
include "resubcld.mm"
include "recnd.mm"
include "abscld.mm"
include "nnrecred.mm"
include "a1i.mm"
include "subfaclim.mm"
include "eluzle.mm"
include "wb.mm"
include "nnre.mm"
include "nngt0.mm"
include "lerec.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "absdifltd.mm"
include "simpld.mm"
include "ltsubaddd.mm"
include "ltled.mm"
include "simprd.mm"
include "ltadd1dd.mm"
include "addassd.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "oveq2i.mm"
include "breqtrd.mm"
include "cz.mm"
include "flbi.mm"
include "mpbir2and.mm"
include "eqcomd.mm"

theorem subfacval3
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cB: class B
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint D n
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint K c
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S m
  disjoint V f
  assert |- ( N e. NN -> ( S ` N ) = ( |_ ` ( ( ( ! ` N ) / _e ) + ( 1 / 2 ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cfa
    cfv
    #
    ceu
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cN
    cS
    cfv
    #
    @0
    @5
    @6
    wceq
    #
    @6
    @4
    cle
    wbr
    #
    @4
    @6
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @6
    @4
    @0
    @6
    @0
    @6
    @0
    cN
    cn0
    wcel
    #
    @6
    cn0
    wcel
    cN
    nnnn0
    #
    cn0
    cn0
    cN
    cS
    vx
    vy
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    subfacf
    ffvelrni
    syl
    nn0zd
    #
    zred
    #
    @0
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @0
    @1
    cr
    wcel
    ceu
    crp
    wcel
    #
    @15
    @0
    @1
    @0
    @11
    @1
    cn
    wcel
    @12
    cN
    faccl
    syl
    nnred
    epr
    @1
    ceu
    rerpdivcl
    sylancl
    #
    halfre
    @2
    @3
    readdcl
    sylancl
    #
    @0
    @6
    @3
    cmin
    co
    @2
    clt
    wbr
    #
    @6
    @4
    clt
    wbr
    @0
    @21
    @2
    @6
    @3
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @2
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    @21
    @23
    wa
    @0
    cN
    c1
    wceq
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    wo
    @26
    cN
    elnn1uz2
    @27
    @26
    @28
    @27
    @25
    c1
    ceu
    cdiv
    co
    #
    @3
    clt
    @27
    @25
    @29
    cabs
    cfv
    #
    @29
    @27
    @24
    @29
    cabs
    @27
    @24
    @29
    cc0
    cmin
    co
    @29
    @27
    @2
    @29
    @6
    cc0
    cmin
    @27
    @1
    c1
    ceu
    cdiv
    @27
    @1
    c1
    cfa
    cfv
    c1
    cN
    c1
    cfa
    fveq2
    fac1
    syl6eq
    oveq1d
    @27
    @6
    c1
    cS
    cfv
    cc0
    cN
    c1
    cS
    fveq2
    vx
    vy
    cD
    cS
    vf
    vn
    derang.d
    subfac.n
    subfac1
    syl6eq
    oveq12d
    @29
    @29
    @29
    crp
    wcel
    #
    @29
    cr
    wcel
    #
    @18
    @31
    epr
    ceu
    rpreccl
    ax-mp
    #
    @29
    rpre
    ax-mp
    #
    recni
    subid1i
    syl6eq
    fveq2d
    @32
    cc0
    @29
    cle
    wbr
    #
    @30
    @29
    wceq
    @34
    @31
    @35
    @33
    @29
    rpge0
    ax-mp
    @29
    absid
    mp2an
    syl6eq
    c2
    ceu
    clt
    wbr
    #
    @29
    @3
    clt
    wbr
    @36
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    c2
    ceu
    2re
    ere
    2pos
    epos
    ltrecii
    mpbi
    syl6eqbr
    @28
    @25
    c1
    cN
    cdiv
    co
    #
    @3
    @28
    @24
    @28
    @0
    @24
    cc
    wcel
    cN
    eluz2nn
    #
    @0
    @24
    @0
    @2
    @6
    @19
    @14
    resubcld
    recnd
    syl
    abscld
    @28
    cN
    @38
    nnrecred
    @16
    @28
    halfre
    a1i
    @28
    @0
    @25
    @37
    clt
    wbr
    @38
    vx
    vy
    cD
    cS
    vf
    vn
    cN
    derang.d
    subfac.n
    subfaclim
    syl
    @28
    c2
    cN
    cle
    wbr
    #
    @37
    @3
    cle
    wbr
    #
    c2
    cN
    eluzle
    @28
    @0
    @39
    @40
    wb
    #
    @38
    @0
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    @41
    cN
    nnre
    cN
    nngt0
    c2
    cr
    wcel
    cc0
    c2
    clt
    wbr
    @42
    @43
    wa
    @41
    2re
    2pos
    c2
    cN
    lerec
    mpanl12
    syl2anc
    syl
    mpbid
    ltletrd
    jaoi
    sylbi
    @0
    @2
    @6
    @3
    @19
    @14
    @16
    @0
    halfre
    a1i
    #
    absdifltd
    mpbid
    #
    simpld
    @0
    @6
    @3
    @2
    @14
    @44
    @19
    ltsubaddd
    mpbid
    ltled
    @0
    @4
    @22
    @3
    caddc
    co
    #
    @9
    clt
    @0
    @2
    @22
    @3
    @19
    @0
    @6
    cr
    wcel
    @16
    @22
    cr
    wcel
    @14
    halfre
    @6
    @3
    readdcl
    sylancl
    @44
    @0
    @21
    @23
    @45
    simprd
    ltadd1dd
    @0
    @46
    @6
    @3
    @3
    caddc
    co
    #
    caddc
    co
    @9
    @0
    @6
    @3
    @3
    @0
    @6
    @14
    recnd
    @0
    @3
    @44
    recnd
    #
    @48
    addassd
    @47
    c1
    @6
    caddc
    c1
    cc
    wcel
    @47
    c1
    wceq
    ax-1cn
    c1
    2halves
    ax-mp
    oveq2i
    syl6eq
    breqtrd
    @0
    @17
    @6
    cz
    wcel
    @7
    @8
    @10
    wa
    wb
    @20
    @13
    @4
    @6
    flbi
    syl2anc
    mpbir2and
    eqcomd
end
