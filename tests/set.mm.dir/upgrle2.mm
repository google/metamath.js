include "cupgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "wfun.mm"
include "cuhgr.mm"
include "upgruhgr.mm"
include "uhgrfun.mm"
include "syl.mm"
include "funfn.mm"
include "sylib.mm"
include "adantr.mm"
include "simpr.mm"
include "cvtx.mm"
include "eqid.mm"
include "upgrle.mm"
include "syl3anc.mm"

theorem upgrle2
  let cG: class G
  let cI: class I
  let cX: class X
  assume upgrle2.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. UPGraph /\ X e. dom I ) -> ( # ` ( I ` X ) ) <_ 2 )

  proof
    cG
    cupgr
    wcel
    #
    cX
    cI
    cdm
    #
    wcel
    #
    wa
    @0
    cI
    @1
    wfn
    #
    @2
    cX
    cI
    cfv
    chash
    cfv
    c2
    cle
    wbr
    @0
    @2
    simpl
    @0
    @3
    @2
    @0
    cI
    wfun
    #
    @3
    @0
    cG
    cuhgr
    wcel
    @4
    cG
    upgruhgr
    cI
    cG
    upgrle2.i
    uhgrfun
    syl
    cI
    funfn
    sylib
    adantr
    @0
    @2
    simpr
    @1
    cI
    cX
    cG
    cG
    cvtx
    cfv
    #
    @5
    eqid
    upgrle2.i
    upgrle
    syl3anc
end
