include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cc.mm"
include "caddc.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "csu.mm"
include "cexp.mm"
include "cmpt.mm"
include "cn0.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "wss.mm"
include "plybss.mm"
include "syl.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "fssd.mm"
include "plymullem1.mm"
include "nn0addcld.mm"
include "eqid.mm"
include "un0addcl.mm"
include "fzfid.mm"
include "wa.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fznn0sub.mm"
include "jca.mm"
include "un0mulcl.mm"
include "caovclg.mm"
include "syldan.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "a1i.mm"
include "fsumcllem.mm"
include "adantr.mm"
include "elplyd.mm"
include "eqeltrd.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem plymullem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  assume plyadd.1: |- ( ph -> F e. ( Poly ` S ) )
  assume plyadd.2: |- ( ph -> G e. ( Poly ` S ) )
  assume plyadd.3: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plyadd.m: |- ( ph -> M e. NN0 )
  assume plyadd.n: |- ( ph -> N e. NN0 )
  assume plyadd.a: |- ( ph -> A e. ( ( S u. { 0 } ) ^m NN0 ) )
  assume plyadd.b: |- ( ph -> B e. ( ( S u. { 0 } ) ^m NN0 ) )
  assume plyadd.a2: |- ( ph -> ( A " ( ZZ>= ` ( M + 1 ) ) ) = { 0 } )
  assume plyadd.b2: |- ( ph -> ( B " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume plyadd.f: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... M ) ( ( A ` k ) x. ( z ^ k ) ) ) )
  assume plyadd.g: |- ( ph -> G = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( B ` k ) x. ( z ^ k ) ) ) )
  assume plymul.x: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint a b
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b j
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint m w
  disjoint F m
  disjoint n w
  disjoint F n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint a k
  disjoint S a
  disjoint b k
  disjoint S b
  disjoint j k
  disjoint S j
  disjoint k w
  disjoint S m
  disjoint S n
  disjoint S w
  disjoint A m
  disjoint A n
  disjoint G a
  disjoint G b
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint N n
  assert |- ( ph -> ( F oF x. G ) e. ( Poly ` S ) )

  proof
    wph
    cF
    cG
    cmul
    cof
    co
    #
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    #
    wph
    @0
    vz
    cc
    cc0
    cM
    cN
    caddc
    co
    #
    cfz
    co
    #
    cc0
    vn
    cv
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    @7
    @9
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    vz
    cv
    @7
    cexp
    co
    cmul
    co
    vn
    csu
    cmpt
    @3
    wph
    vz
    cA
    cB
    cS
    vk
    vn
    cF
    cG
    cM
    cN
    plyadd.1
    plyadd.2
    plyadd.m
    plyadd.n
    wph
    cn0
    @2
    cc
    cA
    wph
    cA
    @2
    cn0
    cmap
    co
    #
    wcel
    #
    cn0
    @2
    cA
    wf
    #
    plyadd.a
    wph
    @2
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    @16
    @17
    wb
    wph
    @2
    cc
    wss
    cc
    cvv
    wcel
    @18
    wph
    cS
    @1
    cc
    wph
    cF
    @4
    wcel
    cS
    cc
    wss
    plyadd.1
    cS
    cF
    plybss
    syl
    #
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    #
    cnex
    @2
    cc
    cvv
    ssexg
    sylancl
    #
    nn0ex
    @2
    cn0
    cA
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    @21
    fssd
    wph
    cn0
    @2
    cc
    cB
    wph
    cB
    @15
    wcel
    #
    cn0
    @2
    cB
    wf
    #
    plyadd.b
    wph
    @18
    @19
    @24
    @25
    wb
    @22
    nn0ex
    @2
    cn0
    cB
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    @21
    fssd
    plyadd.a2
    plyadd.b2
    plyadd.f
    plyadd.g
    plymullem1
    wph
    vz
    @14
    @2
    vn
    @5
    @21
    wph
    cM
    cN
    plyadd.m
    plyadd.n
    nn0addcld
    wph
    @14
    @2
    wcel
    @7
    @6
    wcel
    wph
    vx
    vy
    @8
    @13
    @2
    vk
    @21
    wph
    cS
    @2
    vx
    cv
    #
    vy
    cv
    #
    @20
    @2
    eqid
    #
    plyadd.3
    un0addcl
    wph
    cc0
    @7
    fzfid
    wph
    @9
    @8
    wcel
    #
    @10
    @2
    wcel
    #
    @12
    @2
    wcel
    #
    wa
    @13
    @2
    wcel
    wph
    @30
    wa
    @31
    @32
    wph
    @17
    @9
    cn0
    wcel
    @31
    @30
    @23
    @9
    @7
    elfznn0
    cn0
    @2
    @9
    cA
    ffvelrn
    syl2an
    wph
    @25
    @11
    cn0
    wcel
    @32
    @30
    @26
    @9
    cc0
    @7
    fznn0sub
    cn0
    @2
    @11
    cB
    ffvelrn
    syl2an
    jca
    wph
    vx
    vy
    @10
    @12
    @2
    @2
    @2
    cmul
    wph
    cS
    @2
    @27
    @28
    @20
    @29
    plymul.x
    un0mulcl
    caovclg
    syldan
    cc0
    @2
    wcel
    #
    wph
    @33
    @1
    @2
    wss
    @1
    cS
    ssun2
    cc0
    @2
    c0ex
    snss
    mpbir
    a1i
    fsumcllem
    adantr
    elplyd
    eqeltrd
    cS
    plyun0
    syl6eleq
end
