include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "c1.mm"
include "ccxp.mm"
include "cabs.mm"
include "caddc.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "cbvrabv.mm"
include "infeq1i.mm"
include "eqid.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "cbvsumv.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "ftalem5.mm"

theorem ftalem6
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cD: class D
  let cE: class E
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let cJ: class J
  let cR: class R
  let cT: class T
  let cU: class U
  let cX: class X
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem6.5: |- ( ph -> ( F ` 0 ) =/= 0 )

  disjoint A x
  disjoint N x
  disjoint F x
  disjoint ph x
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k x
  disjoint A k
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint s z
  disjoint D s
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint E r
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint N r
  disjoint N s
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s w
  disjoint s y
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J s
  disjoint J x
  disjoint J z
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S k
  disjoint S s
  disjoint T k
  disjoint T r
  disjoint T x
  disjoint U r
  disjoint U x
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. x e. CC ( abs ` ( F ` x ) ) < ( abs ` ( F ` 0 ) ) )

  proof
    wph
    vx
    cA
    cS
    cc0
    cF
    cfv
    #
    vk
    cv
    #
    cA
    cfv
    #
    cc0
    wne
    #
    vk
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cA
    cfv
    cdiv
    co
    cneg
    c1
    @5
    cdiv
    co
    ccxp
    co
    #
    @0
    cabs
    cfv
    #
    @5
    c1
    caddc
    co
    cN
    cfz
    co
    #
    vr
    cv
    #
    cA
    cfv
    #
    @6
    @9
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    vr
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    vs
    vn
    cF
    @5
    cN
    c1
    @16
    cle
    wbr
    c1
    @16
    cif
    #
    ftalem.1
    ftalem.2
    ftalem.3
    ftalem.4
    ftalem6.5
    cr
    @4
    vn
    cv
    #
    cA
    cfv
    #
    cc0
    wne
    #
    vn
    cn
    crab
    clt
    @3
    @20
    vk
    vn
    cn
    @1
    @18
    wceq
    @2
    @19
    cc0
    @1
    @18
    cA
    fveq2
    neeq1d
    cbvrabv
    infeq1i
    @6
    eqid
    @15
    @8
    vs
    cv
    #
    cA
    cfv
    #
    @6
    @21
    cexp
    co
    #
    cmul
    co
    #
    cabs
    cfv
    #
    vs
    csu
    #
    c1
    caddc
    co
    @7
    cdiv
    @14
    @26
    c1
    caddc
    @8
    @13
    @25
    vr
    vs
    @9
    @21
    wceq
    #
    @12
    @24
    cabs
    @27
    @10
    @22
    @11
    @23
    cmul
    @9
    @21
    cA
    fveq2
    @9
    @21
    @6
    cexp
    oveq2
    oveq12d
    fveq2d
    cbvsumv
    oveq1i
    oveq2i
    @17
    eqid
    ftalem5
end
