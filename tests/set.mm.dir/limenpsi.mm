include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cvv.mm"
include "difexg.mm"
include "cv.mm"
include "csuc.mm"
include "wne.mm"
include "wa.mm"
include "wlim.mm"
include "wb.mm"
include "limsuc.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "nsuceq0.mm"
include "jctir.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "con0.mm"
include "wceq.mm"
include "word.mm"
include "limord.mm"
include "ordelon.mm"
include "mpan.mm"
include "suc11.mm"
include "syl2an.mm"
include "dom3.mm"
include "mpdan.mm"
include "wss.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpi.mm"
include "sbth.mm"
include "syl2anc.mm"

theorem limenpsi
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume limenpsi.1: |- Lim A


  assert |- ( A e. V -> A ~~ ( A \ { (/) } ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    c0
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @2
    cA
    cdom
    wbr
    #
    cA
    @2
    cen
    wbr
    @0
    @2
    cvv
    wcel
    @3
    cA
    @1
    cV
    difexg
    vx
    vy
    cA
    @2
    vx
    cv
    #
    csuc
    #
    vy
    cv
    #
    csuc
    #
    cV
    cvv
    @5
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    @6
    c0
    wne
    #
    wa
    @6
    @2
    wcel
    @9
    @10
    @11
    @9
    @10
    cA
    wlim
    #
    @9
    @10
    wb
    limenpsi.1
    cA
    @5
    limsuc
    ax-mp
    biimpi
    @5
    nsuceq0
    jctir
    @6
    cA
    c0
    eldifsn
    sylibr
    @9
    @5
    con0
    wcel
    #
    @7
    con0
    wcel
    #
    @6
    @8
    wceq
    @5
    @7
    wceq
    wb
    @7
    cA
    wcel
    #
    cA
    word
    #
    @9
    @13
    @12
    @16
    limenpsi.1
    cA
    limord
    ax-mp
    #
    cA
    @5
    ordelon
    mpan
    @16
    @15
    @14
    @17
    cA
    @7
    ordelon
    mpan
    @5
    @7
    suc11
    syl2an
    dom3
    mpdan
    @0
    @2
    cA
    wss
    @4
    cA
    @1
    difss
    @2
    cA
    cV
    ssdomg
    mpi
    cA
    @2
    sbth
    syl2anc
end
