include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "wsmo.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "ccf.mm"
include "wceq.mm"
include "cfcoflem.mm"
include "imp.mm"
include "wf1.mm"
include "cff1.mm"
include "f1f.mm"
include "anim1i.mm"
include "eximi.mm"
include "syl.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "eqid.mm"
include "coftr.mm"
include "syl5com.mm"
include "csuc.mm"
include "word.mm"
include "wi.mm"
include "eloni.mm"
include "cfon.mm"
include "cep.mm"
include "coi.mm"
include "cofsmo.mm"
include "sylancl.mm"
include "3simpb.mm"
include "onsuci.mm"
include "oneli.mm"
include "cfflb.mm"
include "sylan2.mm"
include "syl5.mm"
include "wb.mm"
include "onsssuc.mm"
include "ibir.mm"
include "ad2antlr.mm"
include "sstrd.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "syld.mm"
include "sylan9.mm"
include "eqssd.mm"
include "ex.mm"

theorem cfcof
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vc: setvar c
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v

  disjoint f w
  disjoint f z
  disjoint A f
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B f
  disjoint B w
  disjoint B z
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g k
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint c v
  disjoint B c
  disjoint f v
  disjoint g v
  disjoint B g
  disjoint h v
  disjoint B h
  disjoint k v
  disjoint B k
  disjoint r v
  disjoint B r
  disjoint s v
  disjoint B s
  disjoint t v
  disjoint B t
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint B y
  assert |- ( ( A e. On /\ B e. On ) -> ( E. f ( f : B --> A /\ Smo f /\ A. z e. A E. w e. B z C_ ( f ` w ) ) -> ( cf ` A ) = ( cf ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    vf
    cv
    #
    wf
    @3
    wsmo
    vz
    cv
    vw
    cv
    @3
    cfv
    wss
    vw
    cB
    wrex
    vz
    cA
    wral
    w3a
    vf
    wex
    #
    cA
    ccf
    cfv
    #
    cB
    ccf
    cfv
    #
    wceq
    @2
    @4
    wa
    @5
    @6
    @2
    @4
    @5
    @6
    wss
    vz
    vw
    cA
    cB
    vf
    cfcoflem
    imp
    @2
    @4
    @6
    @5
    wss
    #
    @0
    @4
    @5
    cB
    vh
    cv
    #
    wf
    vr
    cv
    #
    vt
    cv
    #
    @8
    cfv
    #
    wss
    vt
    @5
    wrex
    vr
    cB
    wral
    wa
    vh
    wex
    #
    @1
    @7
    @0
    @5
    cA
    vg
    cv
    #
    wf
    #
    vs
    cv
    #
    @10
    @13
    cfv
    wss
    vt
    @5
    wrex
    vs
    cA
    wral
    #
    wa
    #
    vg
    wex
    #
    @4
    @12
    @0
    @5
    cA
    @13
    wf1
    #
    @16
    wa
    #
    vg
    wex
    @18
    vs
    vt
    cA
    vg
    cff1
    @20
    @17
    vg
    @19
    @14
    @16
    @5
    cA
    @13
    f1f
    anim1i
    eximi
    syl
    vz
    vw
    vs
    vt
    vy
    cA
    cB
    @5
    vf
    vg
    vh
    vv
    vy
    @5
    vy
    cv
    @13
    cfv
    vv
    cv
    @3
    cfv
    wss
    vv
    cB
    crab
    cint
    cmpt
    #
    vr
    @21
    eqid
    coftr
    syl5com
    @1
    @12
    vc
    cv
    #
    cB
    vk
    cv
    #
    wf
    #
    @23
    wsmo
    #
    @9
    @15
    @23
    cfv
    wss
    vs
    @22
    wrex
    vr
    cB
    wral
    #
    w3a
    #
    vk
    wex
    #
    vc
    @5
    csuc
    #
    wrex
    #
    @7
    @1
    cB
    word
    @5
    con0
    wcel
    #
    @12
    @30
    wi
    cB
    eloni
    cA
    cfon
    #
    vc
    vx
    vr
    vt
    vs
    cB
    @5
    @11
    vx
    cv
    #
    @8
    cfv
    wcel
    vt
    @33
    wral
    vx
    @5
    crab
    #
    vh
    vk
    @9
    @22
    @8
    cfv
    wss
    vc
    @5
    crab
    cint
    #
    @34
    cep
    coi
    #
    @34
    eqid
    @35
    eqid
    @36
    eqid
    cofsmo
    sylancl
    @1
    @28
    @7
    vc
    @29
    @1
    @22
    @29
    wcel
    #
    @28
    @7
    @1
    @37
    wa
    #
    @28
    wa
    @6
    @22
    @5
    @38
    @28
    @6
    @22
    wss
    #
    @28
    @24
    @26
    wa
    #
    vk
    wex
    #
    @38
    @39
    @27
    @40
    vk
    @24
    @25
    @26
    3simpb
    eximi
    @37
    @1
    @22
    con0
    wcel
    #
    @41
    @39
    wi
    @29
    @22
    @5
    @32
    onsuci
    oneli
    #
    vr
    vs
    cB
    @22
    vk
    cfflb
    sylan2
    syl5
    imp
    @37
    @22
    @5
    wss
    #
    @1
    @28
    @37
    @44
    @37
    @42
    @31
    @44
    @37
    wb
    @43
    @32
    @22
    @5
    onsssuc
    sylancl
    ibir
    ad2antlr
    sstrd
    exp31
    rexlimdv
    syld
    sylan9
    imp
    eqssd
    ex
end
