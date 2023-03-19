include "cr.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wf.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cif.mm"
include "wral.mm"
include "1ex.mm"
include "prid2.mm"
include "c0ex.mm"
include "prid1.mm"
include "keepel.mm"
include "rgenw.mm"
include "fmpt.mm"
include "mpbi.mm"
include "wa.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "a1i.mm"
include "fmptd.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "fvex.mm"
include "elsn.mm"
include "eleq1.mm"
include "ifbid.mm"
include "ifex.mm"
include "fvmpt.mm"
include "eqeq1d.mm"
include "wn.mm"
include "wne.mm"
include "0ne1.mm"
include "iffalse.mm"
include "necon3bbid.mm"
include "mpbiri.mm"
include "con4i.mm"
include "iftrue.mm"
include "impbii.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "mblss.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "pm3.2i.mm"

theorem i1f1lem
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume i1f1.1: |- F = ( x e. RR |-> if ( x e. A , 1 , 0 ) )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- ( F : RR --> { 0 , 1 } /\ ( A e. dom vol -> ( `' F " { 1 } ) = A ) )

  proof
    cr
    cc0
    c1
    cpr
    #
    cF
    wf
    #
    cA
    cvol
    cdm
    wcel
    #
    cF
    ccnv
    c1
    csn
    #
    cima
    #
    cA
    wceq
    wi
    vx
    cv
    #
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    @0
    wcel
    #
    vx
    cr
    wral
    @1
    @8
    vx
    cr
    @6
    c1
    cc0
    @0
    cc0
    c1
    1ex
    prid2
    cc0
    c1
    c0ex
    prid1
    keepel
    #
    rgenw
    vx
    cr
    @0
    @7
    cF
    i1f1.1
    fmpt
    mpbi
    @2
    vy
    @4
    cA
    @2
    vy
    cv
    #
    @4
    wcel
    #
    @10
    cr
    wcel
    #
    @10
    cA
    wcel
    #
    wa
    #
    @13
    @2
    @11
    @12
    @10
    cF
    cfv
    #
    @3
    wcel
    #
    wa
    #
    @14
    @2
    @1
    cF
    cr
    wfn
    @11
    @17
    wb
    @2
    vx
    cr
    @7
    @0
    cF
    @8
    @2
    @5
    cr
    wcel
    wa
    @9
    a1i
    i1f1.1
    fmptd
    cr
    @0
    cF
    ffn
    cr
    @10
    @3
    cF
    elpreima
    3syl
    @12
    @16
    @13
    @16
    @15
    c1
    wceq
    #
    @12
    @13
    @15
    c1
    @10
    cF
    fvex
    elsn
    @12
    @18
    @13
    c1
    cc0
    cif
    #
    c1
    wceq
    #
    @13
    @12
    @15
    @19
    c1
    vx
    @10
    @7
    @19
    cr
    cF
    @5
    @10
    wceq
    @6
    @13
    c1
    cc0
    @5
    @10
    cA
    eleq1
    ifbid
    i1f1.1
    @13
    c1
    cc0
    1ex
    c0ex
    ifex
    fvmpt
    eqeq1d
    @20
    @13
    @13
    @20
    @13
    wn
    #
    @20
    wn
    cc0
    c1
    wne
    0ne1
    @21
    @20
    cc0
    c1
    @21
    @19
    cc0
    c1
    @13
    c1
    cc0
    iffalse
    eqeq1d
    necon3bbid
    mpbiri
    con4i
    @13
    c1
    cc0
    iftrue
    impbii
    syl6bb
    syl5bb
    pm5.32i
    syl6bb
    @2
    @13
    @12
    @2
    cA
    cr
    @10
    cA
    mblss
    sseld
    pm4.71rd
    bitr4d
    eqrdv
    pm3.2i
end
