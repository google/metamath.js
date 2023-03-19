include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cmpt.mm"
include "ccnp.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-cnp.mm"
include "a1i.mm"
include "simprl.mm"
include "unieqd.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "oveq12d.mm"
include "rexeqdv.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "topontop.mm"
include "adantr.mm"
include "adantl.mm"
include "cpw.mm"
include "wf.mm"
include "ssrab2.mm"
include "ovex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "eqid.mm"
include "fmptd.mm"
include "toponmax.mm"
include "pwex.mm"
include "fex2.mm"
include "syl3anc.mm"
include "ovmpt2d.mm"

theorem cnpfval
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vy: setvar y
  let vu: setvar u

  disjoint f w
  disjoint f x
  disjoint K f
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint X f
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y w
  disjoint Y x
  disjoint f v
  disjoint J f
  disjoint v w
  disjoint v x
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint f j
  disjoint f k
  disjoint f y
  disjoint j k
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint w y
  disjoint x y
  disjoint K y
  disjoint X j
  disjoint X k
  disjoint X y
  disjoint Y j
  disjoint Y k
  disjoint Y y
  disjoint f u
  disjoint j u
  disjoint j v
  disjoint J j
  disjoint k u
  disjoint k v
  disjoint J k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint v y
  disjoint J y
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( J CnP K ) = ( x e. X |-> { f e. ( Y ^m X ) | A. w e. K ( ( f ` x ) e. w -> E. v e. J ( x e. v /\ ( f " v ) C_ w ) ) } ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    vj
    vk
    cJ
    cK
    ctop
    ctop
    vx
    vj
    cv
    #
    cuni
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    vw
    cv
    #
    wcel
    #
    @5
    vv
    cv
    #
    wcel
    @6
    @9
    cima
    @7
    wss
    wa
    #
    vv
    @3
    wrex
    #
    wi
    #
    vw
    vk
    cv
    #
    wral
    #
    vf
    @13
    cuni
    #
    @4
    cmap
    co
    #
    crab
    #
    cmpt
    #
    vx
    cX
    @8
    @10
    vv
    cJ
    wrex
    #
    wi
    #
    vw
    cK
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    cmpt
    #
    ccnp
    cvv
    ccnp
    vj
    vk
    ctop
    ctop
    @18
    cmpt2
    wceq
    @2
    vx
    vw
    vf
    vv
    vj
    vk
    df-cnp
    a1i
    @2
    @3
    cJ
    wceq
    #
    @13
    cK
    wceq
    #
    wa
    #
    wa
    #
    vx
    @4
    @17
    cX
    @23
    @28
    @4
    cJ
    cuni
    #
    cX
    @28
    @3
    cJ
    @2
    @25
    @26
    simprl
    #
    unieqd
    @0
    cX
    @29
    wceq
    @1
    @27
    cX
    cJ
    toponuni
    ad2antrr
    eqtr4d
    #
    @28
    @14
    @21
    vf
    @16
    @22
    @28
    @15
    cY
    @4
    cX
    cmap
    @28
    @15
    cK
    cuni
    #
    cY
    @28
    @13
    cK
    @2
    @25
    @26
    simprr
    #
    unieqd
    @1
    cY
    @32
    wceq
    @0
    @27
    cY
    cK
    toponuni
    ad2antlr
    eqtr4d
    @31
    oveq12d
    @28
    @12
    @20
    vw
    @13
    cK
    @33
    @28
    @11
    @19
    @8
    @28
    @10
    vv
    @3
    cJ
    @30
    rexeqdv
    imbi2d
    raleqbidv
    rabeqbidv
    mpteq12dv
    @0
    cJ
    ctop
    wcel
    @1
    cX
    cJ
    topontop
    adantr
    @1
    cK
    ctop
    wcel
    @0
    cY
    cK
    topontop
    adantl
    @2
    cX
    @22
    cpw
    #
    @24
    wf
    cX
    cJ
    wcel
    #
    @34
    cvv
    wcel
    #
    @24
    cvv
    wcel
    @2
    vx
    cX
    @23
    @34
    @24
    @23
    @34
    wcel
    #
    @2
    @5
    cX
    wcel
    wa
    @37
    @23
    @22
    wss
    @21
    vf
    @22
    ssrab2
    @23
    @22
    cY
    cX
    cmap
    ovex
    #
    elpw2
    mpbir
    a1i
    @24
    eqid
    fmptd
    @0
    @35
    @1
    cX
    cJ
    toponmax
    adantr
    @36
    @2
    @22
    @38
    pwex
    a1i
    cX
    @34
    @24
    cJ
    cvv
    fex2
    syl3anc
    ovmpt2d
end
