include "ccv.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "wss.mm"
include "wa.mm"
include "cat.mm"
include "wrex.mm"
include "wceq.mm"
include "cch.mm"
include "wcel.mm"
include "wi.mm"
include "cvpss.mm"
include "mp2an.mm"
include "chrelati.mm"
include "syl.mm"
include "cvnbtwn2.mm"
include "mp3an12.mm"
include "atelch.mm"
include "chjcl.mm"
include "sylancr.mm"
include "syl11.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem cvati
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A <oH B -> E. x e. HAtoms ( A vH x ) = B )

  proof
    cA
    cB
    ccv
    wbr
    #
    cA
    cA
    vx
    cv
    #
    chj
    co
    #
    wpss
    @2
    cB
    wss
    wa
    #
    vx
    cat
    wrex
    #
    @2
    cB
    wceq
    #
    vx
    cat
    wrex
    @0
    cA
    cB
    wpss
    #
    @4
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @0
    @6
    wi
    chpssat.1
    chpssat.2
    cA
    cB
    cvpss
    mp2an
    vx
    cA
    cB
    chpssat.1
    chpssat.2
    chrelati
    syl
    @0
    @3
    @5
    vx
    cat
    @2
    cch
    wcel
    #
    @0
    @3
    @5
    wi
    #
    @1
    cat
    wcel
    #
    @7
    @8
    @9
    @0
    @10
    wi
    chpssat.1
    chpssat.2
    cA
    cB
    @2
    cvnbtwn2
    mp3an12
    @11
    @7
    @1
    cch
    wcel
    @9
    chpssat.1
    @1
    atelch
    cA
    @1
    chjcl
    sylancr
    syl11
    reximdvai
    mpd
end
