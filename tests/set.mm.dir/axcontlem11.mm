include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "cee.mm"
include "cfv.mm"
include "crab.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "wa.mm"
include "copab.mm"
include "opeq2.mm"
include "breq2d.mm"
include "breq1.mm"
include "orbi12d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "axcontlem1.mm"
include "axcontlem10.mm"

theorem axcontlem11
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let cN: class N
  let cZ: class Z
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vt: setvar t
  let vz: setvar z

  disjoint A b
  disjoint A x
  disjoint b x
  disjoint B b
  disjoint B x
  disjoint B y
  disjoint b y
  disjoint x y
  disjoint N b
  disjoint N x
  disjoint N y
  disjoint U b
  disjoint U x
  disjoint U y
  disjoint Z b
  disjoint Z x
  disjoint Z y
  disjoint A i
  disjoint A j
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint A t
  disjoint A z
  disjoint b i
  disjoint b j
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b t
  disjoint b z
  disjoint i x
  disjoint j x
  disjoint p x
  disjoint q x
  disjoint r x
  disjoint t x
  disjoint x z
  disjoint i j
  disjoint i p
  disjoint i q
  disjoint i r
  disjoint i t
  disjoint i z
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j t
  disjoint j z
  disjoint p q
  disjoint p r
  disjoint p t
  disjoint p z
  disjoint q r
  disjoint q t
  disjoint q z
  disjoint r t
  disjoint r z
  disjoint t z
  disjoint B i
  disjoint B j
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B t
  disjoint B z
  disjoint i y
  disjoint j y
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint t y
  disjoint y z
  disjoint N i
  disjoint N j
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint N t
  disjoint N z
  disjoint U i
  disjoint U j
  disjoint U p
  disjoint U q
  disjoint U r
  disjoint U t
  disjoint U z
  disjoint Z i
  disjoint Z j
  disjoint Z p
  disjoint Z q
  disjoint Z r
  disjoint Z t
  disjoint Z z
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ ( ( Z e. ( EE ` N ) /\ U e. A /\ B =/= (/) ) /\ Z =/= U ) ) -> E. b e. ( EE ` N ) A. x e. A A. y e. B b Btwn <. x , y >. )

  proof
    vx
    vy
    vt
    cA
    cB
    cU
    cZ
    vq
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @0
    cZ
    cU
    cop
    #
    cbtwn
    wbr
    #
    wo
    #
    vq
    cN
    cee
    cfv
    #
    crab
    #
    cU
    vi
    vz
    cv
    #
    @7
    wcel
    vr
    cv
    #
    cc0
    cpnf
    cico
    co
    wcel
    vj
    cv
    #
    @8
    cfv
    c1
    @9
    cmin
    co
    @10
    cZ
    cfv
    cmul
    co
    @9
    @10
    cU
    cfv
    cmul
    co
    caddc
    co
    wceq
    vj
    c1
    cN
    cfz
    co
    wral
    wa
    wa
    vz
    vr
    copab
    #
    cN
    cZ
    vp
    vb
    @5
    cU
    cZ
    vp
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @12
    @3
    cbtwn
    wbr
    #
    wo
    vq
    vp
    @6
    @0
    @12
    wceq
    #
    @2
    @14
    @4
    @15
    @16
    @1
    @13
    cU
    cbtwn
    @0
    @12
    cZ
    opeq2
    breq2d
    @0
    @12
    @3
    cbtwn
    breq1
    orbi12d
    cbvrabv
    vz
    vx
    vr
    @7
    cU
    vj
    vi
    @11
    cN
    cZ
    vt
    @11
    eqid
    axcontlem1
    axcontlem10
end
