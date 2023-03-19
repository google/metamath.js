include "ccphlo.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "cvv.mm"
include "cop.mm"
include "c1st.mm"
include "vafval.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c2nd.mm"
include "smfval.mm"
include "nmcvfval.mm"
include "3pm3.2i.mm"
include "phop.mm"
include "eleq1d.mm"
include "ibi.mm"
include "cnv.mm"
include "bafval.mm"
include "isphg.mm"
include "simplbda.mm"
include "sylancr.mm"
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

theorem phpar
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume phpar.1: |- X = ( BaseSet ` U )
  assume phpar.2: |- G = ( +v ` U )
  assume phpar.4: |- S = ( .sOLD ` U )
  assume phpar.6: |- N = ( normCV ` U )


  assert |- ( ( U e. CPreHilOLD /\ A e. X /\ B e. X ) -> ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

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
    c1
    cneg
    #
    @4
    cS
    co
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
    @8
    cB
    cS
    co
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
    @21
    @2
    @0
    cG
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    cN
    cvv
    wcel
    #
    w3a
    #
    cG
    cS
    cop
    cN
    cop
    #
    ccphlo
    wcel
    #
    @21
    @37
    @38
    @39
    cG
    cU
    c1st
    cfv
    #
    c1st
    cfv
    cvv
    cU
    cG
    phpar.2
    vafval
    @43
    c1st
    fvex
    eqeltri
    cS
    @43
    c2nd
    cfv
    cvv
    cS
    cU
    phpar.4
    smfval
    @43
    c2nd
    fvex
    eqeltri
    cN
    cU
    c2nd
    cfv
    cvv
    cU
    cN
    phpar.6
    nmcvfval
    cU
    c2nd
    fvex
    eqeltri
    3pm3.2i
    @0
    @42
    @0
    cU
    @41
    ccphlo
    cS
    cU
    cG
    cN
    phpar.2
    phpar.4
    phpar.6
    phop
    eleq1d
    ibi
    @40
    @42
    @41
    cnv
    wcel
    @21
    vx
    vy
    cvv
    cvv
    cvv
    cS
    cG
    cN
    cX
    cU
    cG
    cX
    phpar.1
    phpar.2
    bafval
    isphg
    simplbda
    sylancr
    3ad2ant1
    @1
    @2
    @21
    @36
    wi
    @0
    @20
    @36
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
    @9
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
    c2
    @31
    @17
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
    @13
    @50
    @19
    @52
    @53
    @7
    @46
    @12
    @49
    caddc
    @53
    @6
    @45
    c2
    cexp
    @53
    @5
    @44
    cN
    @3
    cA
    @4
    cG
    oveq1
    fveq2d
    oveq1d
    @53
    @11
    @48
    c2
    cexp
    @53
    @10
    @47
    cN
    @3
    cA
    @9
    cG
    oveq1
    fveq2d
    oveq1d
    oveq12d
    @53
    @18
    @51
    c2
    cmul
    @53
    @15
    @31
    @17
    caddc
    @53
    @14
    @30
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
    @50
    @29
    @52
    @35
    @54
    @46
    @24
    @49
    @28
    caddc
    @54
    @45
    @23
    c2
    cexp
    @54
    @44
    @22
    cN
    @4
    cB
    cA
    cG
    oveq2
    fveq2d
    oveq1d
    @54
    @48
    @27
    c2
    cexp
    @54
    @47
    @26
    cN
    @54
    @9
    @25
    cA
    cG
    @4
    cB
    @8
    cS
    oveq2
    oveq2d
    fveq2d
    oveq1d
    oveq12d
    @54
    @51
    @34
    c2
    cmul
    @54
    @17
    @33
    @31
    caddc
    @54
    @16
    @32
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
