include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cpw.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "ineq2.mm"
include "fveq2d.mm"
include "difeq2.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "cab.mm"
include "crab.mm"
include "cres.mm"
include "df-vol.mm"
include "dmeqi.mm"
include "dmres.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "ovolf.mm"
include "fdmi.mm"
include "ineq2i.mm"
include "3eqtri.mm"
include "dfrab2.mm"
include "eqtr4i.mm"
include "elrab2.mm"
include "reex.mm"
include "elpw2.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"
include "anbi12i.mm"

theorem ismbl
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A e. dom vol <-> ( A C_ RR /\ A. x e. ~P RR ( ( vol* ` x ) e. RR -> ( vol* ` x ) = ( ( vol* ` ( x i^i A ) ) + ( vol* ` ( x \ A ) ) ) ) ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    cpw
    #
    wcel
    #
    vx
    cv
    #
    covol
    cfv
    #
    @3
    cA
    cin
    #
    covol
    cfv
    #
    @3
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vx
    covol
    ccnv
    cr
    cima
    #
    wral
    #
    wa
    cA
    cr
    wss
    #
    @4
    cr
    wcel
    #
    @10
    wi
    #
    vx
    @1
    wral
    #
    wa
    @4
    @3
    vy
    cv
    #
    cin
    #
    covol
    cfv
    #
    @3
    @17
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    wceq
    #
    vx
    @11
    wral
    #
    @12
    vy
    cA
    @1
    @0
    @17
    cA
    wceq
    #
    @23
    @10
    vx
    @11
    @25
    @22
    @9
    @4
    @25
    @19
    @6
    @21
    @8
    caddc
    @25
    @18
    @5
    covol
    @17
    cA
    @3
    ineq2
    fveq2d
    @25
    @20
    @7
    covol
    @17
    cA
    @3
    difeq2
    fveq2d
    oveq12d
    eqeq2d
    ralbidv
    @0
    @24
    vy
    cab
    #
    @1
    cin
    #
    @24
    vy
    @1
    crab
    @0
    covol
    @26
    cres
    #
    cdm
    @26
    covol
    cdm
    #
    cin
    @27
    cvol
    @28
    vy
    vx
    df-vol
    dmeqi
    covol
    @26
    dmres
    @29
    @1
    @26
    @1
    cc0
    cpnf
    cicc
    co
    #
    covol
    ovolf
    fdmi
    ineq2i
    3eqtri
    @24
    vy
    @1
    dfrab2
    eqtr4i
    elrab2
    @2
    @13
    @12
    @16
    cA
    cr
    reex
    elpw2
    @10
    @15
    vx
    @11
    @1
    @3
    @11
    wcel
    #
    @10
    wi
    @3
    @1
    wcel
    #
    @14
    wa
    #
    @10
    wi
    @32
    @15
    wi
    @31
    @33
    @10
    @1
    @30
    covol
    wf
    covol
    @1
    wfn
    @31
    @33
    wb
    ovolf
    @1
    @30
    covol
    ffn
    @1
    @3
    cr
    covol
    elpreima
    mp2b
    imbi1i
    @32
    @14
    @10
    impexp
    bitri
    ralbii2
    anbi12i
    bitri
end
