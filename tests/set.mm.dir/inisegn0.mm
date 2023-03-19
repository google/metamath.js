include "crn.mm"
include "wcel.mm"
include "cvv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "c0.mm"
include "wne.mm"
include "elex.mm"
include "wn.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "necon1ai.mm"
include "cv.mm"
include "eleq1.mm"
include "sneq.mm"
include "neeq1d.mm"
include "wbr.mm"
include "cab.mm"
include "wex.mm"
include "abn0.mm"
include "vex.mm"
include "iniseg.mm"
include "ax-mp.mm"
include "neeq1i.mm"
include "elrn.mm"
include "3bitr4ri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem inisegn0
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b


  assert |- ( A e. ran F <-> ( `' F " { A } ) =/= (/) )

  proof
    cA
    cF
    crn
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cF
    ccnv
    #
    cA
    csn
    #
    cima
    #
    c0
    wne
    #
    cA
    @0
    elex
    @2
    @5
    c0
    @2
    wn
    #
    @5
    @3
    c0
    cima
    c0
    @7
    @4
    c0
    @3
    @7
    @4
    c0
    wceq
    cA
    snprc
    biimpi
    imaeq2d
    @3
    ima0
    syl6eq
    necon1ai
    va
    cv
    #
    @0
    wcel
    #
    @3
    @8
    csn
    #
    cima
    #
    c0
    wne
    #
    @1
    @6
    va
    cA
    cvv
    @8
    cA
    @0
    eleq1
    @8
    cA
    wceq
    #
    @11
    @5
    c0
    @13
    @10
    @4
    @3
    @8
    cA
    sneq
    imaeq2d
    neeq1d
    vb
    cv
    @8
    cF
    wbr
    #
    vb
    cab
    #
    c0
    wne
    @14
    vb
    wex
    @12
    @9
    @14
    vb
    abn0
    @11
    @15
    c0
    @8
    cvv
    wcel
    @11
    @15
    wceq
    va
    vex
    #
    vb
    cF
    @8
    cvv
    iniseg
    ax-mp
    neeq1i
    vb
    @8
    cF
    @16
    elrn
    3bitr4ri
    vtoclbg
    pm5.21nii
end
