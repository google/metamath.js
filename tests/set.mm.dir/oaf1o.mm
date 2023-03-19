include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "cdif.mm"
include "wral.mm"
include "wceq.mm"
include "wreu.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wa.mm"
include "oacl.mm"
include "wss.mm"
include "wn.mm"
include "oaword1.mm"
include "wb.mm"
include "ontri1.mm"
include "syldan.mm"
include "mpbid.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "simpl.mm"
include "eldifi.mm"
include "adantl.mm"
include "eldifn.mm"
include "mpbird.mm"
include "oawordeu.mm"
include "syl21anc.mm"
include "eqcom.mm"
include "reubii.mm"
include "sylib.mm"
include "eqid.mm"
include "f1ompt.mm"
include "sylanbrc.mm"

theorem oaf1o
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. On -> ( x e. On |-> ( A +o x ) ) : On -1-1-onto-> ( On \ A ) )

  proof
    cA
    con0
    wcel
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    con0
    cA
    cdif
    #
    wcel
    #
    vx
    con0
    wral
    vy
    cv
    #
    @2
    wceq
    #
    vx
    con0
    wreu
    #
    vy
    @3
    wral
    con0
    @3
    vx
    con0
    @2
    cmpt
    #
    wf1o
    @0
    @4
    vx
    con0
    @0
    @1
    con0
    wcel
    #
    wa
    #
    @2
    con0
    cA
    cA
    @1
    oacl
    #
    @10
    cA
    @2
    wss
    #
    @2
    cA
    wcel
    wn
    #
    cA
    @1
    oaword1
    @0
    @9
    @2
    con0
    wcel
    @12
    @13
    wb
    @11
    cA
    @2
    ontri1
    syldan
    mpbid
    eldifd
    ralrimiva
    @0
    @7
    vy
    @3
    @0
    @5
    @3
    wcel
    #
    wa
    #
    @2
    @5
    wceq
    #
    vx
    con0
    wreu
    #
    @7
    @15
    @0
    @5
    con0
    wcel
    #
    cA
    @5
    wss
    #
    @17
    @0
    @14
    simpl
    @14
    @18
    @0
    @5
    con0
    cA
    eldifi
    adantl
    #
    @15
    @19
    @5
    cA
    wcel
    wn
    #
    @14
    @21
    @0
    @5
    con0
    cA
    eldifn
    adantl
    @0
    @14
    @18
    @19
    @21
    wb
    @20
    cA
    @5
    ontri1
    syldan
    mpbird
    vx
    cA
    @5
    oawordeu
    syl21anc
    @16
    @6
    vx
    con0
    @2
    @5
    eqcom
    reubii
    sylib
    ralrimiva
    vx
    vy
    con0
    @3
    @2
    @8
    @8
    eqid
    f1ompt
    sylanbrc
end
