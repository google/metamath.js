include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "fveq1.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "breq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "cbvrexv.mm"
include "brabga.mm"

theorem wemaplem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }

  disjoint a b
  disjoint a x
  disjoint b x
  disjoint T a
  disjoint T b
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint P a
  disjoint P b
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a c
  disjoint a d
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint B x
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint X a
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P c
  disjoint P d
  disjoint Q c
  disjoint Q d
  disjoint R c
  disjoint R d
  disjoint S c
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ( P e. V /\ Q e. W ) -> ( P T Q <-> E. a e. A ( ( P ` a ) S ( Q ` a ) /\ A. b e. A ( b R a -> ( P ` b ) = ( Q ` b ) ) ) ) )

  proof
    vz
    cv
    #
    vx
    cv
    #
    cfv
    #
    @0
    vy
    cv
    #
    cfv
    #
    cS
    wbr
    #
    vw
    cv
    #
    @0
    cR
    wbr
    #
    @6
    @1
    cfv
    #
    @6
    @3
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    #
    va
    cv
    #
    cP
    cfv
    #
    @15
    cQ
    cfv
    #
    cS
    wbr
    #
    vb
    cv
    #
    @15
    cR
    wbr
    #
    @19
    cP
    cfv
    #
    @19
    cQ
    cfv
    #
    wceq
    #
    wi
    #
    vb
    cA
    wral
    #
    wa
    #
    va
    cA
    wrex
    #
    vx
    vy
    cP
    cQ
    cT
    cV
    cW
    @1
    cP
    wceq
    #
    @3
    cQ
    wceq
    #
    wa
    #
    @14
    @0
    cP
    cfv
    #
    @0
    cQ
    cfv
    #
    cS
    wbr
    #
    @7
    @6
    cP
    cfv
    #
    @6
    cQ
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    @27
    @30
    @13
    @39
    vz
    cA
    @30
    @5
    @33
    @12
    @38
    @28
    @29
    @2
    @31
    @4
    @32
    cS
    @0
    @1
    cP
    fveq1
    @0
    @3
    cQ
    fveq1
    breqan12d
    @30
    @11
    @37
    vw
    cA
    @30
    @10
    @36
    @7
    @28
    @29
    @8
    @34
    @9
    @35
    @6
    @1
    cP
    fveq1
    @6
    @3
    cQ
    fveq1
    eqeqan12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    @39
    @26
    vz
    va
    cA
    vz
    va
    weq
    #
    @33
    @18
    @38
    @25
    @40
    @31
    @16
    @32
    @17
    cS
    @0
    @15
    cP
    fveq2
    @0
    @15
    cQ
    fveq2
    breq12d
    @40
    @38
    @6
    @15
    cR
    wbr
    #
    @36
    wi
    #
    vw
    cA
    wral
    @25
    @40
    @37
    @42
    vw
    cA
    @40
    @7
    @41
    @36
    @0
    @15
    @6
    cR
    breq2
    imbi1d
    ralbidv
    @42
    @24
    vw
    vb
    cA
    vw
    vb
    weq
    #
    @41
    @20
    @36
    @23
    @6
    @19
    @15
    cR
    breq1
    @43
    @34
    @21
    @35
    @22
    @6
    @19
    cP
    fveq2
    @6
    @19
    cQ
    fveq2
    eqeq12d
    imbi12d
    cbvralv
    syl6bb
    anbi12d
    cbvrexv
    syl6bb
    wemapso.t
    brabga
end
