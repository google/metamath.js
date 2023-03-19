include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "clfig.mm"
include "cv.mm"
include "cfn.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wrex.mm"
include "cin.mm"
include "islssfg.mm"
include "wb.mm"
include "wi.mm"
include "wss.mm"
include "lssss.mm"
include "adantl.mm"
include "sstr2.mm"
include "mpan9.mm"
include "lspssid.mm"
include "adantlr.mm"
include "impbida.mm"
include "vex.mm"
include "elpw.mm"
include "3bitr4g.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "pweq.mm"
include "eleq2d.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "mpbii.mm"
include "com12.mm"
include "adantld.mm"
include "pm5.32rd.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitr2i.mm"
include "syl6bb.mm"
include "rexbidv2.mm"
include "bitrd.mm"

theorem islssfg2
  let cB: class B
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let vb: setvar b
  assume islssfg.x: |- X = ( W |`s U )
  assume islssfg.s: |- S = ( LSubSp ` W )
  assume islssfg.n: |- N = ( LSpan ` W )
  assume islssfg2.b: |- B = ( Base ` W )

  disjoint W b
  disjoint X b
  disjoint S b
  disjoint U b
  disjoint N b
  assert |- ( ( W e. LMod /\ U e. S ) -> ( X e. LFinGen <-> E. b e. ( ~P B i^i Fin ) ( N ` b ) = U ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    clfig
    wcel
    vb
    cv
    #
    cfn
    wcel
    #
    @3
    cN
    cfv
    #
    cU
    wceq
    #
    wa
    #
    vb
    cU
    cpw
    #
    wrex
    @6
    vb
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    cS
    cU
    cN
    cW
    cX
    vb
    islssfg.x
    islssfg.s
    islssfg.n
    islssfg
    @2
    @7
    @6
    vb
    @8
    @10
    @2
    @3
    @8
    wcel
    #
    @7
    wa
    @3
    @9
    wcel
    #
    @7
    wa
    #
    @3
    @10
    wcel
    #
    @6
    wa
    #
    @2
    @7
    @11
    @12
    @2
    @6
    @11
    @12
    wb
    #
    @4
    @6
    @2
    @16
    @6
    @0
    @5
    cS
    wcel
    #
    wa
    #
    @3
    @5
    cpw
    #
    wcel
    #
    @12
    wb
    #
    wi
    @2
    @16
    wi
    @18
    @3
    @5
    wss
    #
    @3
    cB
    wss
    #
    @20
    @12
    @18
    @22
    @23
    @18
    @5
    cB
    wss
    #
    @22
    @23
    @17
    @24
    @0
    cS
    @5
    cB
    cW
    islssfg2.b
    islssfg.s
    lssss
    adantl
    @3
    @5
    cB
    sstr2
    mpan9
    @0
    @23
    @22
    @17
    @3
    cN
    cB
    cW
    islssfg2.b
    islssfg.n
    lspssid
    adantlr
    impbida
    @3
    @5
    vb
    vex
    #
    elpw
    @3
    cB
    @25
    elpw
    3bitr4g
    @6
    @18
    @2
    @21
    @16
    @6
    @17
    @1
    @0
    @5
    cU
    cS
    eleq1
    anbi2d
    @6
    @20
    @11
    @12
    @6
    @19
    @8
    @3
    @5
    cU
    pweq
    eleq2d
    bibi1d
    imbi12d
    mpbii
    com12
    adantld
    pm5.32rd
    @15
    @12
    @4
    wa
    #
    @6
    wa
    @13
    @14
    @26
    @6
    @3
    @9
    cfn
    elin
    anbi1i
    @12
    @4
    @6
    anass
    bitr2i
    syl6bb
    rexbidv2
    bitrd
end
