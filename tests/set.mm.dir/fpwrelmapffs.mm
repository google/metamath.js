include "cv.mm"
include "crn.mm"
include "cfn.mm"
include "wss.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cmap.mm"
include "crab.mm"
include "cxp.mm"
include "cres.mm"
include "wf1o.mm"
include "cin.mm"
include "wtru.mm"
include "cfv.mm"
include "copab.mm"
include "fpwrelmap.mm"
include "a1i.mm"
include "wceq.mm"
include "wb.mm"
include "wf.mm"
include "simpl.mm"
include "pwex.mm"
include "elmap.mm"
include "sylib.mm"
include "simpr.mm"
include "fpwrelmapffslem.mm"
include "3adant1.mm"
include "f1oresrab.mm"
include "trud.mm"
include "maprnin.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "rabeqf.mm"
include "ax-mp.mm"
include "rabrab.mm"
include "3eqtri.mm"
include "dfin5.mm"
include "f1oeq23.mm"
include "mp2an.mm"
include "reseq2i.mm"
include "f1oeq1.mm"
include "bitr2i.mm"
include "mpbi.mm"

theorem fpwrelmapffs
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vf: setvar f
  let cM: class M
  let vr: setvar r
  assume fpwrelmap.1: |- A e. _V
  assume fpwrelmap.2: |- B e. _V
  assume fpwrelmap.3: |- M = ( f e. ( ~P B ^m A ) |-> { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } )
  assume fpwrelmapffs.1: |- S = { f e. ( ( ~P B i^i Fin ) ^m A ) | ( f supp (/) ) e. Fin }

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f r
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint B r
  assert |- ( M |` S ) : S -1-1-onto-> ( ~P ( A X. B ) i^i Fin )

  proof
    vf
    cv
    #
    crn
    cfn
    wss
    #
    @0
    c0
    csupp
    co
    cfn
    wcel
    #
    wa
    #
    vf
    cB
    cpw
    #
    cA
    cmap
    co
    #
    crab
    #
    vr
    cv
    #
    cfn
    wcel
    #
    vr
    cA
    cB
    cxp
    cpw
    #
    crab
    #
    cM
    @6
    cres
    #
    wf1o
    #
    cS
    @9
    cfn
    cin
    #
    cM
    cS
    cres
    #
    wf1o
    #
    @12
    wtru
    @3
    @8
    vf
    vr
    @5
    @9
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    @16
    @0
    cfv
    wcel
    wa
    vx
    vy
    copab
    #
    cM
    fpwrelmap.3
    @5
    @9
    cM
    wf1o
    wtru
    vx
    vy
    cA
    cB
    vf
    cM
    fpwrelmap.1
    fpwrelmap.2
    fpwrelmap.3
    fpwrelmap
    a1i
    @0
    @5
    wcel
    #
    @7
    @17
    wceq
    #
    @8
    @3
    wb
    wtru
    @18
    @19
    wa
    #
    vx
    vy
    cA
    cB
    @7
    @0
    fpwrelmap.1
    fpwrelmap.2
    @20
    @18
    cA
    @4
    @0
    wf
    @18
    @19
    simpl
    @4
    cA
    @0
    cB
    fpwrelmap.2
    pwex
    #
    fpwrelmap.1
    elmap
    sylib
    @18
    @19
    simpr
    fpwrelmapffslem
    3adant1
    f1oresrab
    trud
    @15
    @6
    @10
    @14
    wf1o
    #
    @12
    cS
    @6
    wceq
    @13
    @10
    wceq
    @15
    @22
    wb
    cS
    @2
    vf
    @4
    cfn
    cin
    cA
    cmap
    co
    #
    crab
    #
    @2
    vf
    @1
    vf
    @5
    crab
    #
    crab
    #
    @6
    fpwrelmapffs.1
    @23
    @25
    wceq
    @24
    @26
    wceq
    cA
    @4
    cfn
    vf
    fpwrelmap.1
    @21
    maprnin
    @2
    vf
    @23
    @25
    vf
    @23
    nfcv
    @1
    vf
    @5
    nfrab1
    rabeqf
    ax-mp
    @1
    @2
    vf
    @5
    rabrab
    3eqtri
    #
    vr
    @9
    cfn
    dfin5
    cS
    @6
    @13
    @10
    @14
    f1oeq23
    mp2an
    @14
    @11
    wceq
    @22
    @12
    wb
    cS
    @6
    cM
    @27
    reseq2i
    @6
    @10
    @14
    @11
    f1oeq1
    ax-mp
    bitr2i
    mpbi
end
