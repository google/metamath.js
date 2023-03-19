include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cfv.mm"
include "cafv.mm"
include "dmfco.mm"
include "csn.mm"
include "cres.mm"
include "wceq.mm"
include "funres.mm"
include "anim2i.mm"
include "ancoms.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "sylbir.mm"
include "syl.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "bitrd.mm"

theorem dmfcoafv
  let cA: class A
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( Fun G /\ A e. dom G ) -> ( A e. dom ( F o. G ) <-> ( G ''' A ) e. dom F ) )

  proof
    cG
    wfun
    #
    cA
    cG
    cdm
    wcel
    #
    wa
    #
    cA
    cF
    cG
    ccom
    cdm
    wcel
    cA
    cG
    cfv
    #
    cF
    cdm
    #
    wcel
    cA
    cG
    cafv
    #
    @4
    wcel
    cA
    cF
    cG
    dmfco
    @2
    @3
    @5
    @4
    @2
    @5
    @3
    @2
    @1
    cG
    cA
    csn
    #
    cres
    wfun
    #
    wa
    #
    @5
    @3
    wceq
    #
    @1
    @0
    @8
    @0
    @7
    @1
    @6
    cG
    funres
    anim2i
    ancoms
    @8
    cA
    cG
    wdfat
    @9
    cA
    cG
    df-dfat
    cA
    cG
    afvfundmfveq
    sylbir
    syl
    eqcomd
    eleq1d
    bitrd
end
