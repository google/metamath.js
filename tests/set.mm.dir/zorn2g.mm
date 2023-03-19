include "cv.mm"
include "wbr.mm"
include "crn.mm"
include "wral.mm"
include "crab.mm"
include "cvv.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "crecs.mm"
include "cima.mm"
include "wceq.mm"
include "weq.mm"
include "breq1.mm"
include "notbid.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvriotav.mm"
include "rneq.mm"
include "raleqdv.mm"
include "rabbidv.mm"
include "riotaeqbidv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "recseq.mm"
include "ax-mp.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "zorn2lem7.mm"

theorem zorn2g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint R x
  disjoint y z
  disjoint w y
  disjoint R y
  disjoint w z
  disjoint R z
  disjoint R w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint v x
  disjoint u x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint s x
  disjoint r x
  disjoint q x
  disjoint d x
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint v y
  disjoint u y
  disjoint g y
  disjoint h y
  disjoint t y
  disjoint s y
  disjoint r y
  disjoint q y
  disjoint d y
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint v z
  disjoint u z
  disjoint g z
  disjoint h z
  disjoint t z
  disjoint s z
  disjoint r z
  disjoint q z
  disjoint d z
  disjoint k z
  disjoint m z
  disjoint n z
  disjoint v w
  disjoint u w
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint s w
  disjoint r w
  disjoint q w
  disjoint d w
  disjoint k w
  disjoint m w
  disjoint n w
  disjoint u v
  disjoint g v
  disjoint h v
  disjoint t v
  disjoint s v
  disjoint r v
  disjoint q v
  disjoint d v
  disjoint k v
  disjoint m v
  disjoint n v
  disjoint R v
  disjoint g u
  disjoint h u
  disjoint t u
  disjoint s u
  disjoint r u
  disjoint q u
  disjoint d u
  disjoint k u
  disjoint m u
  disjoint n u
  disjoint R u
  disjoint g h
  disjoint g t
  disjoint g s
  disjoint g r
  disjoint g q
  disjoint d g
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint R g
  disjoint h t
  disjoint h s
  disjoint h r
  disjoint h q
  disjoint d h
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint R h
  disjoint s t
  disjoint r t
  disjoint q t
  disjoint d t
  disjoint k t
  disjoint m t
  disjoint n t
  disjoint R t
  disjoint r s
  disjoint q s
  disjoint d s
  disjoint k s
  disjoint m s
  disjoint n s
  disjoint R s
  disjoint q r
  disjoint d r
  disjoint k r
  disjoint m r
  disjoint n r
  disjoint R r
  disjoint d q
  disjoint k q
  disjoint m q
  disjoint n q
  disjoint R q
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint R d
  disjoint k m
  disjoint k n
  disjoint R k
  disjoint m n
  disjoint R m
  disjoint R n
  disjoint A v
  disjoint A u
  disjoint A g
  disjoint A h
  disjoint A t
  disjoint A s
  disjoint A r
  disjoint A q
  disjoint A d
  disjoint A k
  disjoint A m
  disjoint A n
  assert |- ( ( A e. dom card /\ R Po A /\ A. w ( ( w C_ A /\ R Or w ) -> E. x e. A A. z e. w ( z R x \/ z = x ) ) ) -> E. x e. A A. y e. A -. x R y )

  proof
    vu
    vt
    vr
    vq
    vm
    vk
    cA
    vq
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    vq
    vd
    cv
    #
    crn
    #
    wral
    #
    vv
    cA
    crab
    #
    vs
    cv
    #
    vr
    cv
    #
    cR
    wbr
    #
    vs
    vh
    cvv
    vg
    cv
    #
    vn
    cv
    #
    @0
    wbr
    #
    wn
    #
    vg
    @2
    vq
    vh
    cv
    #
    crn
    #
    wral
    #
    vv
    cA
    crab
    #
    wral
    #
    vn
    @17
    crio
    #
    cmpt
    #
    crecs
    #
    vu
    cv
    cima
    wral
    vr
    cA
    crab
    #
    cR
    vd
    vs
    @21
    @9
    vs
    @21
    vt
    cv
    cima
    wral
    vr
    cA
    crab
    #
    vw
    vz
    vx
    vy
    @20
    vd
    cvv
    vk
    cv
    #
    vm
    cv
    #
    @0
    wbr
    #
    wn
    #
    vk
    @6
    wral
    #
    vm
    @6
    crio
    #
    cmpt
    #
    wceq
    @21
    @30
    crecs
    wceq
    vh
    vd
    cvv
    @19
    @29
    vh
    vd
    weq
    #
    @19
    @27
    vk
    @17
    wral
    #
    vm
    @17
    crio
    @29
    @18
    @32
    vn
    vm
    @17
    @18
    @24
    @11
    @0
    wbr
    #
    wn
    #
    vk
    @17
    wral
    vn
    vm
    weq
    #
    @32
    @13
    @34
    vg
    vk
    @17
    vg
    vk
    weq
    @12
    @33
    @10
    @24
    @11
    @0
    breq1
    notbid
    cbvralv
    @35
    @34
    @27
    vk
    @17
    @35
    @33
    @26
    @11
    @25
    @24
    @0
    breq2
    notbid
    ralbidv
    syl5bb
    cbvriotav
    @31
    @32
    @28
    vm
    @17
    @6
    @31
    @16
    @5
    vv
    cA
    @31
    @2
    vq
    @15
    @4
    @14
    @3
    rneq
    raleqdv
    rabbidv
    #
    @31
    @27
    vk
    @17
    @6
    @36
    raleqdv
    riotaeqbidv
    syl5eq
    cbvmptv
    @20
    @30
    recseq
    ax-mp
    @5
    @9
    vs
    @4
    wral
    #
    vv
    vr
    cA
    @5
    @7
    @1
    cR
    wbr
    #
    vs
    @4
    wral
    vv
    vr
    weq
    #
    @37
    @2
    @38
    vq
    vs
    @4
    @0
    @7
    @1
    cR
    breq1
    cbvralv
    @39
    @38
    @9
    vs
    @4
    @1
    @8
    @7
    cR
    breq2
    ralbidv
    syl5bb
    cbvrabv
    @22
    eqid
    @23
    eqid
    zorn2lem7
end
