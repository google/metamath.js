include "ccphlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "phnv.mm"
include "cns.mm"
include "cop.mm"
include "wa.mm"
include "wb.mm"
include "eqid.mm"
include "nvop.mm"
include "eleq1.mm"
include "c1.mm"
include "cneg.mm"
include "cvv.mm"
include "cpv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnmcv.mm"
include "bafval.mm"
include "isphg.mm"
include "mp3an.mm"
include "nvmval.mm"
include "3expa.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "anbi1d.mm"
include "syl5rbb.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "syl.mm"
include "bianabs.mm"
include "biadan2.mm"

theorem isph
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cA: class A
  let cB: class B
  assume isph.1: |- X = ( BaseSet ` U )
  assume isph.2: |- G = ( +v ` U )
  assume isph.3: |- M = ( -v ` U )
  assume isph.6: |- N = ( normCV ` U )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( U e. CPreHilOLD <-> ( U e. NrmCVec /\ A. x e. X A. y e. X ( ( ( N ` ( x G y ) ) ^ 2 ) + ( ( N ` ( x M y ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` x ) ^ 2 ) + ( ( N ` y ) ^ 2 ) ) ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cU
    cnv
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    cN
    cfv
    c2
    cexp
    co
    #
    @2
    @3
    cM
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @2
    cN
    cfv
    c2
    cexp
    co
    @3
    cN
    cfv
    c2
    cexp
    co
    caddc
    co
    cmul
    co
    #
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    cU
    phnv
    @1
    @0
    @12
    @1
    cU
    cG
    cU
    cns
    cfv
    #
    cop
    cN
    cop
    #
    wceq
    #
    @0
    @1
    @12
    wa
    #
    wb
    @13
    cU
    cG
    cN
    isph.2
    @13
    eqid
    #
    isph.6
    nvop
    @15
    @0
    @14
    ccphlo
    wcel
    #
    @16
    cU
    @14
    ccphlo
    eleq1
    @18
    @14
    cnv
    wcel
    #
    @4
    @2
    c1
    cneg
    @3
    @13
    co
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @9
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    #
    @15
    @16
    cG
    cvv
    wcel
    @13
    cvv
    wcel
    cN
    cvv
    wcel
    @18
    @27
    wb
    cG
    cU
    cpv
    cfv
    cvv
    isph.2
    cU
    cpv
    fvex
    eqeltri
    cU
    cns
    fvex
    cN
    cU
    cnmcv
    cfv
    cvv
    isph.6
    cU
    cnmcv
    fvex
    eqeltri
    vx
    vy
    cvv
    cvv
    cvv
    @13
    cG
    cN
    cX
    cU
    cG
    cX
    isph.1
    isph.2
    bafval
    isphg
    mp3an
    @16
    @1
    @26
    wa
    @15
    @27
    @1
    @12
    @26
    @1
    @11
    @25
    vx
    cX
    @1
    @2
    cX
    wcel
    #
    wa
    #
    @10
    @24
    vy
    cX
    @29
    @3
    cX
    wcel
    #
    wa
    #
    @8
    @23
    @9
    @31
    @7
    @22
    @4
    caddc
    @31
    @6
    @21
    c2
    cexp
    @31
    @5
    @20
    cN
    @1
    @28
    @30
    @5
    @20
    wceq
    @2
    @3
    @13
    cU
    cG
    cM
    cX
    isph.1
    isph.2
    @17
    isph.3
    nvmval
    3expa
    fveq2d
    oveq1d
    oveq2d
    eqeq1d
    ralbidva
    ralbidva
    pm5.32i
    @15
    @1
    @19
    @26
    cU
    @14
    cnv
    eleq1
    anbi1d
    syl5rbb
    syl5bb
    bitrd
    syl
    bianabs
    biadan2
end
