include "chlt.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cfv.mm"
include "crab.mm"
include "wss.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "nfra1.mm"
include "nfv.mm"
include "wi.mm"
include "rsp.mm"
include "eleq1a.mm"
include "syl6.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "glbconN.mm"
include "sylan2.mm"
include "fvex.mm"
include "rabbii.mm"
include "df-rab.mm"
include "eqtri.mm"
include "nfan.mm"
include "wb.mm"
include "rspa.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "sylan.mm"
include "syl.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "opcon2b.mm"
include "syl3an1.mm"
include "3expa.mm"
include "syl5rbbr.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "anassrs.mm"
include "rexbida.mm"
include "r19.42v.mm"
include "syl6rbb.mm"
include "abbidv.mm"
include "cbvabv.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem glbconxN
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cU: class U
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume glbcon.b: |- B = ( Base ` K )
  assume glbcon.u: |- U = ( lub ` K )
  assume glbcon.g: |- G = ( glb ` K )
  assume glbcon.o: |- ._|_ = ( oc ` K )

  disjoint B x
  disjoint ._|_ x
  disjoint S x
  disjoint B i
  disjoint I x
  disjoint K i
  disjoint ._|_ i
  disjoint i x
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint ._|_ t
  disjoint ._|_ u
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint ._|_ y
  disjoint ._|_ z
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint I y
  disjoint i y
  assert |- ( ( K e. HL /\ A. i e. I S e. B ) -> ( G ` { x | E. i e. I x = S } ) = ( ._|_ ` ( U ` { x | E. i e. I x = ( ._|_ ` S ) } ) ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cB
    wcel
    #
    vi
    cI
    wral
    #
    wa
    #
    vx
    cv
    #
    cS
    wceq
    #
    vi
    cI
    wrex
    #
    vx
    cab
    #
    cG
    cfv
    #
    vy
    cv
    #
    c.pe
    cfv
    #
    @7
    wcel
    #
    vy
    cB
    crab
    #
    cU
    cfv
    #
    c.pe
    cfv
    #
    @4
    cS
    c.pe
    cfv
    #
    wceq
    #
    vi
    cI
    wrex
    #
    vx
    cab
    #
    cU
    cfv
    #
    c.pe
    cfv
    @2
    @0
    @7
    cB
    wss
    @8
    @14
    wceq
    @2
    vy
    @7
    cB
    @9
    @7
    wcel
    @9
    cS
    wceq
    #
    vi
    cI
    wrex
    #
    @2
    @9
    cB
    wcel
    #
    @6
    @21
    vx
    @9
    vy
    vex
    @4
    @9
    wceq
    @5
    @20
    vi
    cI
    @4
    @9
    cS
    eqeq1
    rexbidv
    elab
    @2
    @20
    @22
    vi
    cI
    @1
    vi
    cI
    nfra1
    #
    @22
    vi
    nfv
    @2
    vi
    cv
    cI
    wcel
    #
    @1
    @20
    @22
    wi
    @1
    vi
    cI
    rsp
    cS
    cB
    @9
    eleq1a
    syl6
    rexlimd
    syl5bi
    ssrdv
    vy
    cB
    @7
    cU
    cG
    cK
    c.pe
    glbcon.b
    glbcon.u
    glbcon.g
    glbcon.o
    glbconN
    sylan2
    @3
    @13
    @19
    c.pe
    @3
    @12
    @18
    cU
    @3
    @12
    @22
    @10
    cS
    wceq
    #
    vi
    cI
    wrex
    #
    wa
    #
    vy
    cab
    #
    @18
    @12
    @26
    vy
    cB
    crab
    @28
    @11
    @26
    vy
    cB
    @6
    @26
    vx
    @10
    @9
    c.pe
    fvex
    @4
    @10
    wceq
    @5
    @25
    vi
    cI
    @4
    @10
    cS
    eqeq1
    rexbidv
    elab
    rabbii
    @26
    vy
    cB
    df-rab
    eqtri
    @3
    @28
    @9
    @15
    wceq
    #
    vi
    cI
    wrex
    #
    vy
    cab
    @18
    @3
    @27
    @30
    vy
    @3
    @30
    @22
    @25
    wa
    #
    vi
    cI
    wrex
    @27
    @3
    @29
    @31
    vi
    cI
    @0
    @2
    vi
    @0
    vi
    nfv
    @23
    nfan
    @0
    @2
    @24
    @29
    @31
    wb
    #
    @2
    @24
    wa
    @0
    @1
    @32
    @1
    vi
    cI
    rspa
    @0
    @1
    wa
    #
    @29
    @22
    @29
    wa
    @31
    @33
    @29
    @22
    @33
    @15
    cB
    wcel
    #
    @29
    @22
    wi
    @0
    cK
    cops
    wcel
    #
    @1
    @34
    cK
    hlop
    #
    cB
    cK
    c.pe
    cS
    glbcon.b
    glbcon.o
    opoccl
    sylan
    @15
    cB
    @9
    eleq1a
    syl
    pm4.71rd
    @33
    @22
    @29
    @25
    @25
    cS
    @10
    wceq
    #
    @33
    @22
    wa
    @29
    cS
    @10
    eqcom
    @0
    @1
    @22
    @37
    @29
    wb
    #
    @0
    @35
    @1
    @22
    @38
    @36
    cB
    cK
    c.pe
    cS
    @9
    glbcon.b
    glbcon.o
    opcon2b
    syl3an1
    3expa
    syl5rbbr
    pm5.32da
    bitrd
    sylan2
    anassrs
    rexbida
    @22
    @25
    vi
    cI
    r19.42v
    syl6rbb
    abbidv
    @30
    @17
    vy
    vx
    @9
    @4
    wceq
    @29
    @16
    vi
    cI
    @9
    @4
    @15
    eqeq1
    rexbidv
    cbvabv
    syl6eq
    syl5eq
    fveq2d
    fveq2d
    eqtrd
end
