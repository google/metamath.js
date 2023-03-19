include "c1.mm"
include "cpr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "disj.mm"
include "wo.mm"
include "wne.mm"
include "wa.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cle.mm"
include "wbr.mm"
include "eldifi.mm"
include "elfzle1.mm"
include "clt.mm"
include "1lt2.mm"
include "1re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "breq2.mm"
include "mtbiri.mm"
include "necon2ai.mm"
include "3syl.mm"
include "eldifsni.mm"
include "jca.mm"
include "eleq2s.mm"
include "neanior.mm"
include "sylib.mm"
include "vex.mm"
include "elpr.mm"
include "sylnibr.mm"
include "mprgbir.mm"
include "a1i.mm"
include "uncom.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "uneq1i.mm"
include "undif1.mm"
include "eqtr2i.mm"
include "uneq12i.mm"
include "df-pr.mm"
include "equncomi.mm"
include "uneq2i.mm"
include "unass.mm"
include "eqtr4i.mm"
include "3eqtr4i.mm"
include "wss.mm"
include "snssd.mm"
include "ssequn2.mm"
include "df-2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "uneq2d.mm"
include "cuz.mm"
include "cn.mm"
include "peano2nnd.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "fzsplit.mm"
include "eqtr4d.mm"
include "syl5eqr.mm"
include "oveq2i.mm"
include "cfn.mm"
include "fzfi.mm"
include "diffi.mm"
include "eqeltri.mm"
include "prfi.mm"
include "hashun.mm"
include "mp3an.mm"
include "fveq2d.mm"
include "neeq1.mm"
include "syl.mm"
include "vtoclga.mm"
include "necomd.mm"
include "cvv.mm"
include "wb.mm"
include "1ex.mm"
include "hashprg.mm"
include "mp2an.mm"
include "oveq2d.mm"
include "3eqtr3a.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "eqtr3d.mm"
include "nncnd.mm"
include "2cnd.mm"
include "cc.mm"
include "hashcl.mm"
include "nn0cni.mm"
include "subadd2d.mm"
include "mpbird.mm"
include "1cnd.mm"
include "pnpcan2d.mm"
include "3jca.mm"

theorem subfacp1lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cB: class B
  let cC: class C
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }
  assume subfacp1lem1.n: |- ( ph -> N e. NN )
  assume subfacp1lem1.m: |- ( ph -> M e. ( 2 ... ( N + 1 ) ) )
  assume subfacp1lem1.x: |- M e. _V
  assume subfacp1lem1.k: |- K = ( ( 2 ... ( N + 1 ) ) \ { M } )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M x
  disjoint M y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
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
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
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
  disjoint K c
  disjoint M b
  disjoint M g
  disjoint S m
  disjoint V f
  assert |- ( ph -> ( ( K i^i { 1 , M } ) = (/) /\ ( K u. { 1 , M } ) = ( 1 ... ( N + 1 ) ) /\ ( # ` K ) = ( N - 1 ) ) )

  proof
    wph
    cK
    c1
    cM
    cpr
    #
    cin
    c0
    wceq
    #
    cK
    @0
    cun
    #
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    wceq
    cK
    chash
    cfv
    #
    cN
    c1
    cmin
    co
    #
    wceq
    @1
    wph
    @1
    vx
    cv
    #
    @0
    wcel
    #
    wn
    vx
    cK
    vx
    cK
    @0
    disj
    @7
    cK
    wcel
    #
    @7
    c1
    wceq
    #
    @7
    cM
    wceq
    wo
    #
    @8
    @9
    @7
    c1
    wne
    #
    @7
    cM
    wne
    #
    wa
    #
    @11
    wn
    @14
    @7
    c2
    @3
    cfz
    co
    #
    cM
    csn
    #
    cdif
    #
    cK
    @7
    @17
    wcel
    #
    @12
    @13
    @18
    @7
    @15
    wcel
    #
    c2
    @7
    cle
    wbr
    #
    @12
    @7
    @15
    @16
    eldifi
    @7
    c2
    @3
    elfzle1
    #
    @20
    @7
    c1
    @10
    @20
    c2
    c1
    cle
    wbr
    #
    c1
    c2
    clt
    wbr
    @22
    wn
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    @7
    c1
    c2
    cle
    breq2
    mtbiri
    necon2ai
    #
    3syl
    @7
    @15
    cM
    eldifsni
    jca
    subfacp1lem1.k
    eleq2s
    @7
    c1
    @7
    cM
    neanior
    sylib
    @7
    c1
    cM
    vx
    vex
    elpr
    sylnibr
    mprgbir
    #
    a1i
    wph
    @2
    c1
    c1
    cfz
    co
    #
    @15
    @16
    cun
    #
    cun
    #
    @4
    c1
    csn
    #
    cK
    @16
    cun
    #
    cun
    @29
    @28
    cun
    #
    @27
    @2
    @28
    @29
    uncom
    @25
    @28
    @26
    @29
    c1
    cz
    wcel
    @25
    @28
    wceq
    1z
    c1
    fzsn
    ax-mp
    @29
    @17
    @16
    cun
    @26
    cK
    @17
    @16
    subfacp1lem1.k
    uneq1i
    @15
    @16
    undif1
    eqtr2i
    uneq12i
    @2
    cK
    @16
    @28
    cun
    #
    cun
    @30
    @0
    @31
    cK
    @0
    @28
    @16
    c1
    cM
    df-pr
    equncomi
    uneq2i
    cK
    @16
    @28
    unass
    eqtr4i
    3eqtr4i
    wph
    @27
    @25
    c1
    c1
    caddc
    co
    #
    @3
    cfz
    co
    #
    cun
    #
    @4
    wph
    @26
    @33
    @25
    wph
    @26
    @15
    @33
    wph
    @16
    @15
    wss
    @26
    @15
    wceq
    wph
    cM
    @15
    subfacp1lem1.m
    snssd
    @16
    @15
    ssequn2
    sylib
    c2
    @32
    @3
    cfz
    df-2
    oveq1i
    syl6eq
    uneq2d
    wph
    @3
    c1
    cuz
    cfv
    #
    wcel
    c1
    @4
    wcel
    @4
    @34
    wceq
    wph
    @3
    cn
    @35
    wph
    cN
    subfacp1lem1.n
    peano2nnd
    #
    nnuz
    syl6eleq
    c1
    @3
    eluzfz1
    c1
    c1
    @3
    fzsplit
    3syl
    eqtr4d
    syl5eqr
    #
    wph
    @3
    c2
    cmin
    co
    #
    @3
    @32
    cmin
    co
    @5
    @6
    c2
    @32
    @3
    cmin
    df-2
    oveq2i
    wph
    @38
    @5
    wceq
    @5
    c2
    caddc
    co
    #
    @3
    wceq
    wph
    @4
    chash
    cfv
    #
    @39
    @3
    wph
    @2
    chash
    cfv
    #
    @5
    @0
    chash
    cfv
    #
    caddc
    co
    #
    @40
    @39
    cK
    cfn
    wcel
    #
    @0
    cfn
    wcel
    @1
    @41
    @43
    wceq
    cK
    @17
    cfn
    subfacp1lem1.k
    @15
    cfn
    wcel
    @17
    cfn
    wcel
    c2
    @3
    fzfi
    @15
    @16
    diffi
    ax-mp
    eqeltri
    #
    c1
    cM
    prfi
    @24
    cK
    @0
    hashun
    mp3an
    wph
    @2
    @4
    chash
    @37
    fveq2d
    wph
    @42
    c2
    @5
    caddc
    wph
    c1
    cM
    wne
    #
    @42
    c2
    wceq
    #
    wph
    cM
    c1
    wph
    cM
    @15
    wcel
    cM
    c1
    wne
    #
    subfacp1lem1.m
    @12
    @48
    vx
    cM
    @15
    @7
    cM
    c1
    neeq1
    @19
    @20
    @12
    @21
    @23
    syl
    vtoclga
    syl
    necomd
    c1
    cvv
    wcel
    cM
    cvv
    wcel
    @46
    @47
    wb
    1ex
    subfacp1lem1.x
    c1
    cM
    cvv
    cvv
    hashprg
    mp2an
    sylib
    oveq2d
    3eqtr3a
    wph
    @3
    cn0
    wcel
    @40
    @3
    wceq
    wph
    @3
    @36
    nnnn0d
    @3
    hashfz1
    syl
    eqtr3d
    wph
    @3
    c2
    @5
    wph
    @3
    @36
    nncnd
    wph
    2cnd
    @5
    cc
    wcel
    wph
    @5
    @44
    @5
    cn0
    wcel
    @45
    cK
    hashcl
    ax-mp
    nn0cni
    a1i
    subadd2d
    mpbird
    wph
    cN
    c1
    c1
    wph
    cN
    subfacp1lem1.n
    nncnd
    wph
    1cnd
    #
    @49
    pnpcan2d
    3eqtr3a
    3jca
end
