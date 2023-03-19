include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cn.mm"
include "ccld.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "cnt.mm"
include "cv.mm"
include "wrex.mm"
include "simpll.mm"
include "simprl.mm"
include "ctop.mm"
include "ctopon.mm"
include "cme.mm"
include "cxmt.mm"
include "cmetmet.mm"
include "ad2antrr.mm"
include "metxmet.mm"
include "mopntopon.mm"
include "3syl.mm"
include "topontop.mm"
include "syl.mm"
include "simprr.mm"
include "toponmax.mm"
include "eqeltrd.mm"
include "isopn3i.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simplr.mm"
include "eqnetrd.mm"
include "bcth.mm"
include "syl3anc.mm"

theorem bcth2
  let cD: class D
  let vk: setvar k
  let cJ: class J
  let cM: class M
  let cX: class X
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cF: class F
  let wph: wff ph
  let cR: class R
  assume bcth.2: |- J = ( MetOpen ` D )

  disjoint D k
  disjoint J k
  disjoint M k
  disjoint X k
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint D n
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint M g
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( ( D e. ( CMet ` X ) /\ X =/= (/) ) /\ ( M : NN --> ( Clsd ` J ) /\ U. ran M = X ) ) -> E. k e. NN ( ( int ` J ) ` ( M ` k ) ) =/= (/) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cX
    c0
    wne
    #
    wa
    #
    cn
    cJ
    ccld
    cfv
    cM
    wf
    #
    cM
    crn
    cuni
    #
    cX
    wceq
    #
    wa
    #
    wa
    #
    @0
    @3
    @4
    cJ
    cnt
    cfv
    #
    cfv
    #
    c0
    wne
    vk
    cv
    cM
    cfv
    @8
    cfv
    c0
    wne
    vk
    cn
    wrex
    @0
    @1
    @6
    simpll
    @2
    @3
    @5
    simprl
    @7
    @9
    cX
    c0
    @7
    @9
    @4
    cX
    @7
    cJ
    ctop
    wcel
    #
    @4
    cJ
    wcel
    @9
    @4
    wceq
    @7
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @10
    @7
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    @11
    @0
    @12
    @1
    @6
    cD
    cX
    cmetmet
    ad2antrr
    cD
    cX
    metxmet
    cD
    cJ
    cX
    bcth.2
    mopntopon
    3syl
    #
    cX
    cJ
    topontop
    syl
    @7
    @4
    cX
    cJ
    @2
    @3
    @5
    simprr
    #
    @7
    @11
    cX
    cJ
    wcel
    @13
    cX
    cJ
    toponmax
    syl
    eqeltrd
    @4
    cJ
    isopn3i
    syl2anc
    @14
    eqtrd
    @0
    @1
    @6
    simplr
    eqnetrd
    cD
    vk
    cJ
    cM
    cX
    bcth.2
    bcth
    syl3anc
end
