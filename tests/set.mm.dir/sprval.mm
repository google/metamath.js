include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cvv.mm"
include "cspr.mm"
include "cmpt.mm"
include "df-spr.mm"
include "a1i.mm"
include "wa.mm"
include "wb.mm"
include "id.mm"
include "rexeq.mm"
include "rexeqbidv.mm"
include "adantl.mm"
include "abbidv.mm"
include "elex.mm"
include "wral.mm"
include "weu.mm"
include "zfpair2.mm"
include "eueq.mm"
include "mpbi.mm"
include "euabex.mm"
include "mp1i.mm"
include "ralrimivw.mm"
include "abrexex2g.mm"
include "mpdan.mm"
include "fvmptd.mm"

theorem sprval
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint V p
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint V v
  disjoint a v
  disjoint b v
  disjoint p v
  disjoint W v
  disjoint k x
  assert |- ( V e. W -> ( Pairs ` V ) = { p | E. a e. V E. b e. V p = { a , b } } )

  proof
    cV
    cW
    wcel
    #
    vv
    cV
    vp
    cv
    va
    cv
    vb
    cv
    cpr
    #
    wceq
    #
    vb
    vv
    cv
    #
    wrex
    #
    va
    @3
    wrex
    #
    vp
    cab
    #
    @2
    vb
    cV
    wrex
    #
    va
    cV
    wrex
    #
    vp
    cab
    #
    cvv
    cspr
    cvv
    cspr
    vv
    cvv
    @6
    cmpt
    wceq
    @0
    vv
    vp
    va
    vb
    df-spr
    a1i
    @0
    @3
    cV
    wceq
    #
    wa
    @5
    @8
    vp
    @10
    @5
    @8
    wb
    @0
    @10
    @4
    @7
    va
    @3
    cV
    @10
    id
    @2
    vb
    @3
    cV
    rexeq
    rexeqbidv
    adantl
    abbidv
    cV
    cW
    elex
    @0
    @7
    vp
    cab
    cvv
    wcel
    #
    va
    cV
    wral
    @9
    cvv
    wcel
    @0
    @11
    va
    cV
    @0
    @2
    vp
    cab
    cvv
    wcel
    #
    vb
    cV
    wral
    @11
    @0
    @12
    vb
    cV
    @2
    vp
    weu
    #
    @12
    @0
    @1
    cvv
    wcel
    @13
    va
    vb
    zfpair2
    vp
    @1
    eueq
    mpbi
    @2
    vp
    euabex
    mp1i
    ralrimivw
    @2
    vb
    vp
    cV
    cW
    cvv
    abrexex2g
    mpdan
    ralrimivw
    @7
    va
    vp
    cV
    cW
    cvv
    abrexex2g
    mpdan
    fvmptd
end
