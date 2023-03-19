include "wfo.mm"
include "crn.mm"
include "wfn.mm"
include "wf.mm"
include "msrf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn4.mm"
include "mpbi.mm"
include "wceq.mm"
include "wb.mm"
include "mstaval.mm"
include "foeq3.mm"
include "mpbir.mm"

theorem msrfo
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let cX: class X
  assume mstaval.r: |- R = ( mStRed ` T )
  assume mstaval.s: |- S = ( mStat ` T )
  assume msrfo.p: |- P = ( mPreSt ` T )


  assert |- R : P -onto-> S

  proof
    cP
    cS
    cR
    wfo
    #
    cP
    cR
    crn
    #
    cR
    wfo
    #
    cR
    cP
    wfn
    #
    @2
    cP
    cP
    cR
    wf
    @3
    cP
    cR
    cT
    msrfo.p
    mstaval.r
    msrf
    cP
    cP
    cR
    ffn
    ax-mp
    cP
    cR
    dffn4
    mpbi
    cS
    @1
    wceq
    @0
    @2
    wb
    cR
    cS
    cT
    mstaval.r
    mstaval.s
    mstaval
    cS
    @1
    cP
    cR
    foeq3
    ax-mp
    mpbir
end
