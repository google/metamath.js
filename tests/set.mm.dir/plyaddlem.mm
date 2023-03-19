include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cc.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
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
include "plyaddlem1.mm"
include "ifcld.mm"
include "eqid.mm"
include "un0addcl.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "elplyd.mm"
include "eqeltrd.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem plyaddlem
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
  assert |- ( ph -> ( F oF + G ) e. ( Poly ` S ) )

  proof
    wph
    cF
    cG
    caddc
    cof
    #
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
    @1
    vz
    cc
    cc0
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cB
    @0
    co
    #
    cfv
    #
    vz
    cv
    @9
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    @4
    wph
    vz
    cA
    cB
    cS
    vk
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
    @3
    cc
    cA
    wph
    cA
    @3
    cn0
    cmap
    co
    #
    wcel
    #
    cn0
    @3
    cA
    wf
    #
    plyadd.a
    wph
    @3
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    @13
    @14
    wb
    wph
    @3
    cc
    wss
    cc
    cvv
    wcel
    @15
    wph
    cS
    @2
    cc
    wph
    cF
    @5
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
    @3
    cc
    cvv
    ssexg
    sylancl
    #
    nn0ex
    @3
    cn0
    cA
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    @18
    fssd
    wph
    cn0
    @3
    cc
    cB
    wph
    cB
    @12
    wcel
    #
    cn0
    @3
    cB
    wf
    #
    plyadd.b
    wph
    @15
    @16
    @21
    @22
    wb
    @19
    nn0ex
    @3
    cn0
    cB
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    @18
    fssd
    plyadd.a2
    plyadd.b2
    plyadd.f
    plyadd.g
    plyaddlem1
    wph
    vz
    @11
    @3
    vk
    @7
    @18
    wph
    @6
    cN
    cM
    cn0
    plyadd.n
    plyadd.m
    ifcld
    wph
    cn0
    @3
    @10
    wf
    @9
    cn0
    wcel
    @11
    @3
    wcel
    @9
    @8
    wcel
    wph
    vx
    vy
    cn0
    cn0
    cn0
    caddc
    @3
    @3
    @3
    cA
    cB
    cvv
    cvv
    wph
    cS
    @3
    vx
    cv
    vy
    cv
    @17
    @3
    eqid
    plyadd.3
    un0addcl
    @20
    @23
    @16
    wph
    nn0ex
    a1i
    #
    @24
    cn0
    inidm
    off
    @9
    @7
    elfznn0
    cn0
    @3
    @9
    @10
    ffvelrn
    syl2an
    elplyd
    eqeltrd
    cS
    plyun0
    syl6eleq
end
