include "cc.mm"
include "c1.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "cply.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "wceq.mm"
include "cnex.mm"
include "a1i.mm"
include "plyf.mm"
include "syl.mm"
include "ofnegsub.mm"
include "syl3anc.mm"
include "wss.mm"
include "plybss.mm"
include "plyconst.mm"
include "syl2anc.mm"
include "plymul.mm"
include "plyadd.mm"
include "eqeltrrd.mm"

theorem plysub
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vj: setvar j
  let vw: setvar w
  let cA: class A
  let cM: class M
  let cN: class N
  assume plyadd.1: |- ( ph -> F e. ( Poly ` S ) )
  assume plyadd.2: |- ( ph -> G e. ( Poly ` S ) )
  assume plyadd.3: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x + y ) e. S )
  assume plymul.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x x. y ) e. S )
  assume plysub.5: |- ( ph -> -u 1 e. S )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
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
  disjoint F z
  disjoint a k
  disjoint S a
  disjoint b k
  disjoint S b
  disjoint j k
  disjoint S j
  disjoint k w
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S w
  disjoint S z
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G a
  disjoint G b
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G w
  disjoint G z
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint M z
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N z
  assert |- ( ph -> ( F oF - G ) e. ( Poly ` S ) )

  proof
    wph
    cF
    cc
    c1
    cneg
    #
    csn
    cxp
    #
    cG
    cmul
    cof
    co
    #
    caddc
    cof
    co
    #
    cF
    cG
    cmin
    cof
    co
    #
    cS
    cply
    cfv
    #
    wph
    cc
    cvv
    wcel
    #
    cc
    cc
    cF
    wf
    #
    cc
    cc
    cG
    wf
    #
    @3
    @4
    wceq
    @6
    wph
    cnex
    a1i
    wph
    cF
    @5
    wcel
    #
    @7
    plyadd.1
    cS
    cF
    plyf
    syl
    wph
    cG
    @5
    wcel
    @8
    plyadd.2
    cS
    cG
    plyf
    syl
    cc
    cF
    cG
    cvv
    ofnegsub
    syl3anc
    wph
    vx
    vy
    cS
    cF
    @2
    plyadd.1
    wph
    vx
    vy
    cS
    @1
    cG
    wph
    cS
    cc
    wss
    #
    @0
    cS
    wcel
    @1
    @5
    wcel
    wph
    @9
    @10
    plyadd.1
    cS
    cF
    plybss
    syl
    plysub.5
    @0
    cS
    plyconst
    syl2anc
    plyadd.2
    plyadd.3
    plymul.4
    plymul
    plyadd.3
    plyadd
    eqeltrrd
end
