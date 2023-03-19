include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "w3a.mm"
include "ccom.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "fnfun.mm"
include "funco.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wa.mm"
include "fndm.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "dmcosseq.mm"
include "syl.mm"
include "3adant2.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fnco
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( ( F Fn A /\ G Fn B /\ ran G C_ A ) -> ( F o. G ) Fn B )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    cG
    crn
    #
    cA
    wss
    #
    w3a
    #
    cF
    cG
    ccom
    #
    wfun
    #
    @5
    cdm
    #
    cB
    wceq
    @5
    cB
    wfn
    @0
    @1
    @6
    @3
    @0
    cF
    wfun
    cG
    wfun
    @6
    @1
    cA
    cF
    fnfun
    cB
    cG
    fnfun
    cF
    cG
    funco
    syl2an
    3adant3
    @4
    @7
    cG
    cdm
    #
    cB
    @0
    @3
    @7
    @8
    wceq
    #
    @1
    @0
    @3
    wa
    @2
    cF
    cdm
    #
    wss
    #
    @9
    @0
    @11
    @3
    @0
    @10
    cA
    @2
    cA
    cF
    fndm
    sseq2d
    biimpar
    cF
    cG
    dmcosseq
    syl
    3adant2
    @1
    @0
    @8
    cB
    wceq
    @3
    cB
    cG
    fndm
    3ad2ant2
    eqtrd
    @5
    cB
    df-fn
    sylanbrc
end
