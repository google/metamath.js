include "ccphlo.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cnv.mm"
include "isph.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "wi.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "3adant1.mm"
include "mpd.mm"

theorem phpar2
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume isph.1: |- X = ( BaseSet ` U )
  assume isph.2: |- G = ( +v ` U )
  assume isph.3: |- M = ( -v ` U )
  assume isph.6: |- N = ( normCV ` U )


  assert |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) -> ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

  proof
    cU
    ccphlo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    vx
    cv
    #
    vy
    cv
    #
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
    @3
    @4
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
    @3
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @4
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
    cmul
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cA
    cB
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
    cA
    cB
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
    cA
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cB
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
    cmul
    co
    #
    wceq
    #
    @0
    @1
    @19
    @2
    @0
    cU
    cnv
    wcel
    @19
    vx
    vy
    cU
    cG
    cM
    cN
    cX
    isph.1
    isph.2
    isph.3
    isph.6
    isph
    simprbi
    3ad2ant1
    @1
    @2
    @19
    @33
    wi
    @0
    @18
    @33
    cA
    @4
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
    cA
    @4
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
    @28
    @15
    caddc
    co
    #
    cmul
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @3
    cA
    wceq
    #
    @11
    @40
    @17
    @42
    @43
    @7
    @36
    @10
    @39
    caddc
    @43
    @6
    @35
    c2
    cexp
    @43
    @5
    @34
    cN
    @3
    cA
    @4
    cG
    oveq1
    fveq2d
    oveq1d
    @43
    @9
    @38
    c2
    cexp
    @43
    @8
    @37
    cN
    @3
    cA
    @4
    cM
    oveq1
    fveq2d
    oveq1d
    oveq12d
    @43
    @16
    @41
    c2
    cmul
    @43
    @13
    @28
    @15
    caddc
    @43
    @12
    @27
    c2
    cexp
    @3
    cA
    cN
    fveq2
    oveq1d
    oveq1d
    oveq2d
    eqeq12d
    @4
    cB
    wceq
    #
    @40
    @26
    @42
    @32
    @44
    @36
    @22
    @39
    @25
    caddc
    @44
    @35
    @21
    c2
    cexp
    @44
    @34
    @20
    cN
    @4
    cB
    cA
    cG
    oveq2
    fveq2d
    oveq1d
    @44
    @38
    @24
    c2
    cexp
    @44
    @37
    @23
    cN
    @4
    cB
    cA
    cM
    oveq2
    fveq2d
    oveq1d
    oveq12d
    @44
    @41
    @31
    c2
    cmul
    @44
    @15
    @30
    @28
    caddc
    @44
    @14
    @29
    c2
    cexp
    @4
    cB
    cN
    fveq2
    oveq1d
    oveq2d
    oveq2d
    eqeq12d
    rspc2v
    3adant1
    mpd
end
