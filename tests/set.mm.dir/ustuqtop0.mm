include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cpw.mm"
include "wa.mm"
include "wss.mm"
include "wral.mm"
include "ustimasn.mm"
include "3expa.mm"
include "an32s.mm"
include "vex.mm"
include "imaex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "wb.mm"
include "cvv.mm"
include "mptexg.mm"
include "rnexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "fmptd.mm"

theorem ustuqtop0
  let vv: setvar v
  let cU: class U
  let cN: class N
  let cX: class X
  let vp: setvar p
  let cA: class A
  let vw: setvar w
  let vq: setvar q
  let cP: class P
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vj: setvar j
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  assume utopustuq.1: |- N = ( p e. X |-> ran ( v e. U |-> ( v " { p } ) ) )

  disjoint p v
  disjoint U p
  disjoint U v
  disjoint X p
  disjoint X v
  disjoint N p
  disjoint A w
  disjoint q v
  disjoint q w
  disjoint P q
  disjoint v w
  disjoint P v
  disjoint P w
  disjoint p q
  disjoint p w
  disjoint U q
  disjoint U w
  disjoint X q
  disjoint a b
  disjoint a c
  disjoint a j
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a u
  disjoint a w
  disjoint N a
  disjoint b c
  disjoint b j
  disjoint b p
  disjoint b q
  disjoint b r
  disjoint b u
  disjoint b w
  disjoint N b
  disjoint c j
  disjoint c p
  disjoint c q
  disjoint c r
  disjoint c u
  disjoint c w
  disjoint N c
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j u
  disjoint j w
  disjoint N j
  disjoint p r
  disjoint p u
  disjoint q r
  disjoint q u
  disjoint N q
  disjoint r u
  disjoint r w
  disjoint N r
  disjoint u w
  disjoint N u
  disjoint N w
  disjoint a v
  disjoint a x
  disjoint U a
  disjoint b v
  disjoint b x
  disjoint U b
  disjoint j v
  disjoint j x
  disjoint U j
  disjoint p x
  disjoint q x
  disjoint r v
  disjoint r x
  disjoint U r
  disjoint u v
  disjoint u x
  disjoint U u
  disjoint v x
  disjoint w x
  disjoint U x
  disjoint X a
  disjoint X b
  disjoint c v
  disjoint X c
  disjoint X j
  disjoint X r
  disjoint X u
  disjoint X w
  assert |- ( U e. ( UnifOn ` X ) -> N : X --> ~P ~P X )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    vp
    cX
    vv
    cU
    vv
    cv
    #
    vp
    cv
    #
    csn
    #
    cima
    #
    cmpt
    #
    crn
    #
    cX
    cpw
    #
    cpw
    #
    cN
    @1
    @3
    cX
    wcel
    #
    wa
    #
    @7
    @9
    wcel
    #
    @7
    @8
    wss
    #
    @11
    @5
    @8
    wcel
    #
    vv
    cU
    wral
    @13
    @11
    @14
    vv
    cU
    @11
    @2
    cU
    wcel
    #
    wa
    @5
    cX
    wss
    #
    @14
    @1
    @15
    @10
    @16
    @1
    @15
    @10
    @16
    @3
    cU
    @2
    cX
    ustimasn
    3expa
    an32s
    @5
    cX
    @2
    @4
    vv
    vex
    imaex
    elpw
    sylibr
    ralrimiva
    vv
    cU
    @5
    @8
    @6
    @6
    eqid
    rnmptss
    syl
    @1
    @12
    @13
    wb
    #
    @10
    @1
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @17
    vv
    cU
    @5
    @0
    mptexg
    @6
    cvv
    rnexg
    @7
    @8
    cvv
    elpwg
    3syl
    adantr
    mpbird
    utopustuq.1
    fmptd
end
