include "chil.mm"
include "wcel.mm"
include "cado.mm"
include "cfv.mm"
include "cno.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "cnop.mm"
include "cmul.mm"
include "cle.mm"
include "cdm.mm"
include "cbo.mm"
include "bdopssadj.mm"
include "sselii.mm"
include "adjvalval.mm"
include "mpan.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "inss1.mm"
include "lncnbd.mm"
include "eleqtrri.mm"
include "inss2.mm"
include "eqeq2d.mm"
include "cbvriotav.mm"
include "cnlnadjlem7.mm"
include "eqbrtrd.mm"

theorem nmopadjlei
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  assume nmopadjle.1: |- T e. BndLinOp


  assert |- ( A e. ~H -> ( normh ` ( ( adjh ` T ) ` A ) ) <_ ( ( normop ` T ) x. ( normh ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cT
    cado
    cfv
    cfv
    #
    cno
    cfv
    cA
    vz
    chil
    vv
    cv
    #
    cT
    cfv
    #
    vz
    cv
    #
    csp
    co
    #
    @2
    vf
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vf
    chil
    crio
    #
    cmpt
    #
    cfv
    #
    cno
    cfv
    cT
    cnop
    cfv
    cA
    cno
    cfv
    cmul
    co
    cle
    @0
    @1
    @12
    cno
    @0
    @1
    @3
    cA
    csp
    co
    #
    @7
    wceq
    #
    vv
    chil
    wral
    #
    vf
    chil
    crio
    #
    @12
    cT
    cado
    cdm
    #
    wcel
    @0
    @1
    @16
    wceq
    cbo
    @17
    cT
    bdopssadj
    nmopadjle.1
    sselii
    vv
    vf
    cA
    cT
    adjvalval
    mpan
    vz
    cA
    @10
    @16
    chil
    @11
    @4
    cA
    wceq
    #
    @9
    @15
    vf
    chil
    @18
    @8
    @14
    vv
    chil
    @18
    @5
    @13
    @7
    @4
    cA
    @3
    csp
    oveq2
    eqeq1d
    ralbidv
    riotabidv
    @11
    eqid
    #
    @15
    vf
    chil
    riotaex
    fvmpt
    eqtr4d
    fveq2d
    vz
    vw
    vv
    cA
    @10
    cT
    vg
    @11
    vg
    chil
    vg
    cv
    cT
    cfv
    @4
    csp
    co
    cmpt
    #
    clo
    ccop
    cin
    #
    clo
    cT
    clo
    ccop
    inss1
    cT
    cbo
    @21
    nmopadjle.1
    lncnbd
    eleqtrri
    #
    sselii
    @21
    ccop
    cT
    clo
    ccop
    inss2
    @22
    sselii
    @20
    eqid
    @9
    @5
    @2
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    vf
    vw
    chil
    @6
    @23
    wceq
    #
    @8
    @25
    vv
    chil
    @26
    @7
    @24
    @5
    @6
    @23
    @2
    csp
    oveq2
    eqeq2d
    ralbidv
    cbvriotav
    @19
    cnlnadjlem7
    eqbrtrd
end
