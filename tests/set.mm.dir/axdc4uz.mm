include "wcel.mm"
include "cxp.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "eleq2.mm"
include "xpeq2.mm"
include "pweq.mm"
include "difeq1d.mm"
include "feq23d.mm"
include "anbi12d.mm"
include "feq3.mm"
include "3anbi1d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cmpt2.mm"
include "vex.mm"
include "eqid.mm"
include "axdc4uzlem.mm"
include "vtoclg.mm"
include "3impib.mm"

theorem axdc4uz
  let cA: class A
  let cC: class C
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume axdc4uz.1: |- M e. ZZ
  assume axdc4uz.2: |- Z = ( ZZ>= ` M )

  disjoint g k
  disjoint A g
  disjoint A k
  disjoint C g
  disjoint F g
  disjoint F k
  disjoint M g
  disjoint M k
  disjoint Z g
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint C f
  disjoint C m
  disjoint F f
  disjoint F n
  disjoint F x
  disjoint f y
  disjoint M f
  disjoint g y
  disjoint k y
  disjoint n y
  disjoint M n
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint Z f
  disjoint Z n
  disjoint Z x
  assert |- ( ( A e. V /\ C e. A /\ F : ( Z X. A ) --> ( ~P A \ { (/) } ) ) -> E. g ( g : Z --> A /\ ( g ` M ) = C /\ A. k e. Z ( g ` ( k + 1 ) ) e. ( k F ( g ` k ) ) ) )

  proof
    cA
    cV
    wcel
    cC
    cA
    wcel
    #
    cZ
    cA
    cxp
    #
    cA
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cF
    wf
    #
    cZ
    cA
    vg
    cv
    #
    wf
    #
    cM
    @6
    cfv
    cC
    wceq
    #
    vk
    cv
    #
    c1
    caddc
    co
    @6
    cfv
    @9
    @9
    @6
    cfv
    cF
    co
    wcel
    vk
    cZ
    wral
    #
    w3a
    #
    vg
    wex
    #
    cC
    vf
    cv
    #
    wcel
    #
    cZ
    @13
    cxp
    #
    @13
    cpw
    #
    @3
    cdif
    #
    cF
    wf
    #
    wa
    #
    cZ
    @13
    @6
    wf
    #
    @8
    @10
    w3a
    #
    vg
    wex
    #
    wi
    @0
    @5
    wa
    #
    @12
    wi
    vf
    cA
    cV
    @13
    cA
    wceq
    #
    @19
    @23
    @22
    @12
    @24
    @14
    @0
    @18
    @5
    @13
    cA
    cC
    eleq2
    @24
    @15
    @17
    @1
    @4
    cF
    @13
    cA
    cZ
    xpeq2
    @24
    @16
    @2
    @3
    @13
    cA
    pweq
    difeq1d
    feq23d
    anbi12d
    @24
    @21
    @11
    vg
    @24
    @20
    @7
    @8
    @10
    @13
    cA
    cZ
    @6
    feq3
    3anbi1d
    exbidv
    imbi12d
    vx
    vy
    @13
    cC
    vg
    vk
    vn
    cF
    vy
    cvv
    vy
    cv
    c1
    caddc
    co
    cmpt
    cM
    crdg
    com
    cres
    #
    vn
    vx
    com
    @13
    vn
    cv
    @25
    cfv
    vx
    cv
    cF
    co
    cmpt2
    #
    cM
    cZ
    axdc4uz.1
    axdc4uz.2
    vf
    vex
    @25
    eqid
    @26
    eqid
    axdc4uzlem
    vtoclg
    3impib
end
