include "cuhgr.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "wa.mm"
include "wf.mm"
include "cdm.mm"
include "eqid.mm"
include "uhgrf.mm"
include "fndm.mm"
include "feq2d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "ffvelrnda.mm"
include "3impa.mm"
include "eldifsni.mm"
include "syl.mm"

theorem uhgrn0
  let cA: class A
  let cE: class E
  let cF: class F
  let cG: class G
  assume uhgrfun.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. UHGraph /\ E Fn A /\ F e. A ) -> ( E ` F ) =/= (/) )

  proof
    cG
    cuhgr
    wcel
    #
    cE
    cA
    wfn
    #
    cF
    cA
    wcel
    #
    w3a
    cF
    cE
    cfv
    #
    cG
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    cdif
    #
    wcel
    #
    @3
    c0
    wne
    @0
    @1
    @2
    @7
    @0
    @1
    wa
    cA
    @6
    cF
    cE
    @0
    @1
    cA
    @6
    cE
    wf
    #
    @0
    cE
    cdm
    #
    @6
    cE
    wf
    @1
    @8
    cE
    cG
    @4
    @4
    eqid
    uhgrfun.e
    uhgrf
    @1
    @9
    cA
    @6
    cE
    cA
    cE
    fndm
    feq2d
    syl5ibcom
    imp
    ffvelrnda
    3impa
    @3
    @5
    c0
    eldifsni
    syl
end
