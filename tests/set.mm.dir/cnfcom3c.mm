include "com.mm"
include "ccnf.mm"
include "co.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "cfv.mm"
include "c0.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt.mm"
include "cun.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "cuni.mm"
include "ccom.mm"
include "eqid.mm"
include "cnfcom3clem.mm"

theorem cnfcom3c
  let vw: setvar w
  let cA: class A
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z

  disjoint b g
  disjoint b w
  disjoint A b
  disjoint g w
  disjoint A g
  disjoint A w
  disjoint b f
  disjoint b k
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b z
  disjoint f g
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g z
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A x
  disjoint A z
  assert |- ( A e. On -> E. g A. b e. A ( _om C_ b -> E. w e. ( On \ 1o ) ( g ` b ) : b -1-1-onto-> ( _om ^o w ) ) )

  proof
    vx
    vz
    vw
    vv
    vu
    cA
    com
    cA
    ccnf
    co
    #
    cdm
    #
    vk
    vf
    cvv
    cvv
    vx
    com
    vk
    cv
    vb
    cv
    @0
    ccnv
    cfv
    #
    c0
    csupp
    co
    cep
    coi
    #
    cfv
    #
    coe
    co
    @4
    @2
    cfv
    comu
    co
    #
    vf
    cv
    cdm
    #
    vx
    cv
    #
    coa
    co
    cmpt
    vx
    @6
    @5
    @7
    coa
    co
    cmpt
    ccnv
    cun
    #
    cmpt2
    c0
    cseqom
    #
    vf
    vg
    vk
    @2
    @3
    vk
    vz
    cvv
    cvv
    @5
    vz
    cv
    coa
    co
    cmpt2
    c0
    cseqom
    #
    @8
    vb
    com
    cA
    coe
    co
    vu
    vv
    @3
    cdm
    #
    cuni
    @3
    cfv
    #
    @2
    cfv
    #
    com
    @12
    coe
    co
    #
    @13
    vv
    cv
    #
    comu
    co
    vu
    cv
    #
    coa
    co
    cmpt2
    #
    vu
    vv
    @13
    @14
    @14
    @16
    comu
    co
    @15
    coa
    co
    cmpt2
    #
    ccnv
    ccom
    @11
    @9
    cfv
    ccom
    #
    cmpt
    #
    @5
    @19
    @12
    @17
    @18
    vb
    @1
    eqid
    @2
    eqid
    @3
    eqid
    @10
    eqid
    @9
    eqid
    @5
    eqid
    @8
    eqid
    @12
    eqid
    @17
    eqid
    @18
    eqid
    @19
    eqid
    @20
    eqid
    cnfcom3clem
end
