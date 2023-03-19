include "wcel.mm"
include "cnv.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "cn0v.mm"
include "wi.mm"
include "c1st.mm"
include "c2nd.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "w3a.mm"
include "cop.mm"
include "cvc.mm"
include "cr.mm"
include "wf.mm"
include "cns.mm"
include "eqid.mm"
include "smfval.mm"
include "eqcomi.mm"
include "nvi.mm"
include "simp3d.mm"
include "simp3.mm"
include "ralimi.mm"
include "syl.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5.mm"
include "3impia.mm"
include "3comr.mm"

theorem nvtri
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvtri.1: |- X = ( BaseSet ` U )
  assume nvtri.2: |- G = ( +v ` U )
  assume nvtri.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( N ` ( A G B ) ) <_ ( ( N ` A ) + ( N ` B ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cU
    cnv
    wcel
    #
    cA
    cB
    cG
    co
    #
    cN
    cfv
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    @0
    @1
    @2
    @8
    @2
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
    @9
    cN
    cfv
    #
    @10
    cN
    cfv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @0
    @1
    wa
    @8
    @2
    @13
    cc0
    wceq
    @9
    cU
    cn0v
    cfv
    #
    wceq
    wi
    #
    @10
    @9
    cU
    c1st
    cfv
    c2nd
    cfv
    #
    co
    cN
    cfv
    @10
    cabs
    cfv
    @13
    cmul
    co
    wceq
    vy
    cc
    wral
    #
    @17
    w3a
    #
    vx
    cX
    wral
    #
    @18
    @2
    cG
    @21
    cop
    cvc
    wcel
    cX
    cr
    cN
    wf
    @24
    vx
    vy
    @21
    cU
    cG
    cN
    cX
    @19
    nvtri.1
    nvtri.2
    cU
    cns
    cfv
    #
    @21
    @25
    cU
    @25
    eqid
    smfval
    eqcomi
    @19
    eqid
    nvtri.6
    nvi
    simp3d
    @23
    @17
    vx
    cX
    @20
    @22
    @17
    simp3
    ralimi
    syl
    @16
    @8
    cA
    @10
    cG
    co
    #
    cN
    cfv
    #
    @5
    @14
    caddc
    co
    #
    cle
    wbr
    vx
    vy
    cA
    cB
    cX
    cX
    @9
    cA
    wceq
    #
    @12
    @27
    @15
    @28
    cle
    @29
    @11
    @26
    cN
    @9
    cA
    @10
    cG
    oveq1
    fveq2d
    @29
    @13
    @5
    @14
    caddc
    @9
    cA
    cN
    fveq2
    oveq1d
    breq12d
    @10
    cB
    wceq
    #
    @27
    @4
    @28
    @7
    cle
    @30
    @26
    @3
    cN
    @10
    cB
    cA
    cG
    oveq2
    fveq2d
    @30
    @14
    @6
    @5
    caddc
    @10
    cB
    cN
    fveq2
    oveq2d
    breq12d
    rspc2v
    syl5
    3impia
    3comr
end
