include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfn.mm"
include "clspn.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "cpw.mm"
include "wrex.mm"
include "clfig.mm"
include "wb.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "ressbas2.mm"
include "syl.mm"
include "pweqd.mm"
include "rexeqdv.mm"
include "adantl.mm"
include "elpwi.mm"
include "lsslsp.mm"
include "3expa.mm"
include "sylan2.mm"
include "ad2antlr.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "lsslmod.mm"
include "islmodfg.mm"
include "3bitr4rd.mm"

theorem islssfg
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  let vb: setvar b
  assume islssfg.x: |- X = ( W |`s U )
  assume islssfg.s: |- S = ( LSubSp ` W )
  assume islssfg.n: |- N = ( LSpan ` W )

  disjoint W b
  disjoint X b
  disjoint S b
  disjoint U b
  disjoint N b
  assert |- ( ( W e. LMod /\ U e. S ) -> ( X e. LFinGen <-> E. b e. ~P U ( b e. Fin /\ ( N ` b ) = U ) ) )

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
    vb
    cv
    #
    cfn
    wcel
    #
    @3
    cX
    clspn
    cfv
    #
    cfv
    #
    cX
    cbs
    cfv
    #
    wceq
    #
    wa
    #
    vb
    cU
    cpw
    #
    wrex
    #
    @9
    vb
    @7
    cpw
    #
    wrex
    #
    @4
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
    @10
    wrex
    cX
    clfig
    wcel
    #
    @1
    @11
    @13
    wb
    @0
    @1
    @9
    vb
    @10
    @12
    @1
    cU
    @7
    @1
    cU
    cW
    cbs
    cfv
    #
    wss
    cU
    @7
    wceq
    #
    cS
    cU
    @18
    cW
    @18
    eqid
    #
    islssfg.s
    lssss
    cU
    @18
    cX
    cW
    islssfg.x
    @20
    ressbas2
    syl
    #
    pweqd
    rexeqdv
    adantl
    @2
    @16
    @9
    vb
    @10
    @2
    @3
    @10
    wcel
    #
    wa
    #
    @15
    @8
    @4
    @23
    @14
    @6
    cU
    @7
    @22
    @2
    @3
    cU
    wss
    #
    @14
    @6
    wceq
    #
    @3
    cU
    elpwi
    @0
    @1
    @24
    @25
    cU
    @3
    cS
    cN
    @5
    cW
    cX
    islssfg.x
    islssfg.n
    @5
    eqid
    #
    islssfg.s
    lsslsp
    3expa
    sylan2
    @1
    @19
    @0
    @22
    @21
    ad2antlr
    eqeq12d
    anbi2d
    rexbidva
    @2
    cX
    clmod
    wcel
    @17
    @13
    wb
    cS
    cU
    cW
    cX
    islssfg.x
    islssfg.s
    lsslmod
    @7
    @5
    cX
    vb
    @7
    eqid
    @26
    islmodfg
    syl
    3bitr4rd
end
