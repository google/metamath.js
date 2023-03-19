include "wfo.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "crn.mm"
include "cres.mm"
include "wfun.mm"
include "wceq.mm"
include "fofun.mm"
include "funcocnv2.mm"
include "syl.mm"
include "forn.mm"
include "reseq2d.mm"
include "eqtrd.mm"

theorem fococnv2
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> ( F o. `' F ) = ( _I |` B ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cF
    cF
    ccnv
    ccom
    #
    cid
    cF
    crn
    #
    cres
    #
    cid
    cB
    cres
    @0
    cF
    wfun
    @1
    @3
    wceq
    cA
    cB
    cF
    fofun
    cF
    funcocnv2
    syl
    @0
    @2
    cB
    cid
    cA
    cB
    cF
    forn
    reseq2d
    eqtrd
end
