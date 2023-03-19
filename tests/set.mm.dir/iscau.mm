include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cca.mm"
include "cv.mm"
include "cuz.mm"
include "cbl.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "cc.mm"
include "cpm.mm"
include "crab.mm"
include "wa.mm"
include "caufval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "reseq1.mm"
include "eqidd.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "feq123d.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem iscau
  let vx: setvar x
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cX: class X
  let vd: setvar d
  let vf: setvar f
  let vj: setvar j
  let vm: setvar m
  let wph: wff ph
  let cM: class M
  let cZ: class Z

  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F k
  disjoint F x
  disjoint X k
  disjoint X x
  disjoint d f
  disjoint d j
  disjoint d k
  disjoint d m
  disjoint d x
  disjoint D d
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint D f
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint D j
  disjoint k m
  disjoint m x
  disjoint D m
  disjoint F f
  disjoint F j
  disjoint F m
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint X d
  disjoint X f
  disjoint X j
  disjoint X m
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint Z x
  assert |- ( D e. ( *Met ` X ) -> ( F e. ( Cau ` D ) <-> ( F e. ( X ^pm CC ) /\ A. x e. RR+ E. k e. ZZ ( F |` ( ZZ>= ` k ) ) : ( ZZ>= ` k ) --> ( ( F ` k ) ( ball ` D ) x ) ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cF
    cD
    cca
    cfv
    #
    wcel
    cF
    vk
    cv
    #
    cuz
    cfv
    #
    @2
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @4
    @3
    cres
    #
    wf
    #
    vk
    cz
    wrex
    #
    vx
    crp
    wral
    #
    vf
    cX
    cc
    cpm
    co
    #
    crab
    #
    wcel
    cF
    @13
    wcel
    @3
    @2
    cF
    cfv
    #
    @6
    @7
    co
    #
    cF
    @3
    cres
    #
    wf
    #
    vk
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @0
    @1
    @14
    cF
    vx
    cD
    vf
    vk
    cX
    caufval
    eleq2d
    @12
    @20
    vf
    cF
    @13
    @4
    cF
    wceq
    #
    @11
    @19
    vx
    crp
    @21
    @10
    @18
    vk
    cz
    @21
    @3
    @3
    @8
    @16
    @9
    @17
    @4
    cF
    @3
    reseq1
    @21
    @3
    eqidd
    @21
    @5
    @15
    @6
    @7
    @2
    @4
    cF
    fveq1
    oveq1d
    feq123d
    rexbidv
    ralbidv
    elrab
    syl6bb
end
