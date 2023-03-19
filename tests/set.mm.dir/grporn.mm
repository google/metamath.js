include "cxp.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "cgr.mm"
include "wcel.mm"
include "wfo.mm"
include "eqid.mm"
include "grpofo.mm"
include "fofun.mm"
include "mp2b.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "fofn.mm"
include "wa.mm"
include "fndmu.mm"
include "xpid11.mm"
include "sylib.mm"
include "mp2an.mm"

theorem grporn
  let cG: class G
  let cX: class X
  assume grprn.1: |- G e. GrpOp
  assume grprn.2: |- dom G = ( X X. X )


  assert |- X = ran G

  proof
    cG
    cX
    cX
    cxp
    #
    wfn
    #
    cG
    cG
    crn
    #
    @2
    cxp
    #
    wfn
    #
    cX
    @2
    wceq
    #
    @1
    cG
    wfun
    #
    cG
    cdm
    @0
    wceq
    cG
    cgr
    wcel
    #
    @3
    @2
    cG
    wfo
    #
    @6
    grprn.1
    cG
    @2
    @2
    eqid
    grpofo
    #
    @3
    @2
    cG
    fofun
    mp2b
    grprn.2
    cG
    @0
    df-fn
    mpbir2an
    @7
    @8
    @4
    grprn.1
    @9
    @3
    @2
    cG
    fofn
    mp2b
    @1
    @4
    wa
    @0
    @3
    wceq
    @5
    @0
    @3
    cG
    fndmu
    cX
    @2
    xpid11
    sylib
    mp2an
end
