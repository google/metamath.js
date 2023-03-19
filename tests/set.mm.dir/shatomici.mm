include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "c0v.mm"
include "wrex.mm"
include "wss.mm"
include "cat.mm"
include "shne0i.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "chil.mm"
include "sheli.mm"
include "h1da.mm"
include "sylan.mm"
include "csh.mm"
include "sh1dle.mm"
include "mpan.mm"
include "adantr.mm"
include "sseq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem shatomici
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume shatomic.1: |- A e. SH

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A =/= 0H -> E. x e. HAtoms x C_ A )

  proof
    cA
    c0h
    wne
    vy
    cv
    #
    c0v
    wne
    #
    vy
    cA
    wrex
    vx
    cv
    #
    cA
    wss
    #
    vx
    cat
    wrex
    #
    vy
    cA
    shatomic.1
    shne0i
    @1
    @4
    vy
    cA
    @0
    cA
    wcel
    #
    @1
    wa
    @0
    csn
    cort
    cfv
    cort
    cfv
    #
    cat
    wcel
    #
    @6
    cA
    wss
    #
    @4
    @5
    @0
    chil
    wcel
    @1
    @7
    @0
    cA
    shatomic.1
    sheli
    @0
    h1da
    sylan
    @5
    @8
    @1
    cA
    csh
    wcel
    @5
    @8
    shatomic.1
    cA
    @0
    sh1dle
    mpan
    adantr
    @3
    @8
    vx
    @6
    cat
    @2
    @6
    cA
    sseq1
    rspcev
    syl2anc
    rexlimiva
    sylbi
end
