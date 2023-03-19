include "cumgr.mm"
include "wcel.mm"
include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c1.mm"
include "wne.mm"
include "ciedg.mm"
include "cdm.mm"
include "c2.mm"
include "cv.mm"
include "cle.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf.mm"
include "wi.mm"
include "cupgr.mm"
include "eqid.mm"
include "umgrislfupgr.mm"
include "simprbi.mm"
include "lfgrn1cycl.mm"
include "syl.mm"
include "imp.mm"

theorem umgrn1cycl
  let cP: class P
  let cF: class F
  let cG: class G
  let vx: setvar x


  assert |- ( ( G e. UMGraph /\ F ( Cycles ` G ) P ) -> ( # ` F ) =/= 1 )

  proof
    cG
    cumgr
    wcel
    #
    cF
    cP
    cG
    ccycls
    cfv
    wbr
    #
    cF
    chash
    cfv
    c1
    wne
    #
    @0
    cG
    ciedg
    cfv
    #
    cdm
    c2
    vx
    cv
    chash
    cfv
    cle
    wbr
    vx
    cG
    cvtx
    cfv
    #
    cpw
    crab
    @3
    wf
    #
    @1
    @2
    wi
    @0
    cG
    cupgr
    wcel
    @5
    vx
    cG
    @3
    @4
    @4
    eqid
    #
    @3
    eqid
    #
    umgrislfupgr
    simprbi
    vx
    cP
    cF
    cG
    @3
    @4
    @6
    @7
    lfgrn1cycl
    syl
    imp
end
