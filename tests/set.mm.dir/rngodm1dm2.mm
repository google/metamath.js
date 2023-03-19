include "crngo.mm"
include "wcel.mm"
include "crn.mm"
include "cxp.mm"
include "wfo.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "cgr.mm"
include "rngogrpo.mm"
include "eqid.mm"
include "grpofo.mm"
include "syl.mm"
include "rngosm.mm"
include "fof.mm"
include "fdm.mm"
include "wi.mm"
include "wa.mm"
include "eqtr.mm"
include "dmeqd.mm"
include "expcom.mm"
include "eqcoms.mm"
include "syl5com.mm"
include "sylc.mm"

theorem rngodm1dm2
  let cR: class R
  let cG: class G
  let cH: class H
  assume rnplrnml0.1: |- H = ( 2nd ` R )
  assume rnplrnml0.2: |- G = ( 1st ` R )


  assert |- ( R e. RingOps -> dom dom G = dom dom H )

  proof
    cR
    crngo
    wcel
    #
    cG
    crn
    #
    @1
    cxp
    #
    @1
    cG
    wfo
    #
    @2
    @1
    cH
    wf
    #
    cG
    cdm
    #
    cdm
    cH
    cdm
    #
    cdm
    wceq
    #
    @0
    cG
    cgr
    wcel
    @3
    cR
    cG
    rnplrnml0.2
    rngogrpo
    cG
    @1
    @1
    eqid
    #
    grpofo
    syl
    cR
    cG
    cH
    @1
    rnplrnml0.2
    rnplrnml0.1
    @8
    rngosm
    @3
    @5
    @2
    wceq
    #
    @4
    @7
    @3
    @2
    @1
    cG
    wf
    @9
    @2
    @1
    cG
    fof
    @2
    @1
    cG
    fdm
    syl
    @4
    @6
    @2
    wceq
    @9
    @7
    wi
    #
    @2
    @1
    cH
    fdm
    @10
    @2
    @6
    @9
    @2
    @6
    wceq
    #
    @7
    @9
    @11
    wa
    @5
    @6
    @5
    @2
    @6
    eqtr
    dmeqd
    expcom
    eqcoms
    syl
    syl5com
    sylc
end
