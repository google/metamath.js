include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wf.mm"
include "cocv.mm"
include "cpj1.mm"
include "co.mm"
include "clss.mm"
include "eqid.mm"
include "pjdm.mm"
include "simprbi.mm"
include "pjval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem pjf
  let cT: class T
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume pjf.k: |- K = ( proj ` W )
  assume pjf.v: |- V = ( Base ` W )


  assert |- ( T e. dom K -> ( K ` T ) : V --> V )

  proof
    cT
    cK
    cdm
    wcel
    #
    cV
    cV
    cT
    cK
    cfv
    #
    wf
    cV
    cV
    cT
    cT
    cW
    cocv
    cfv
    #
    cfv
    cW
    cpj1
    cfv
    #
    co
    #
    wf
    #
    @0
    cT
    cW
    clss
    cfv
    #
    wcel
    @5
    @3
    cT
    cK
    @6
    @2
    cV
    cW
    pjf.v
    @6
    eqid
    @2
    eqid
    #
    @3
    eqid
    #
    pjf.k
    pjdm
    simprbi
    @0
    cV
    cV
    @1
    @4
    @3
    cT
    cK
    @2
    cW
    @7
    @8
    pjf.k
    pjval
    feq1d
    mpbird
end
