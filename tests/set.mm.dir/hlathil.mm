include "cdvh.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "ccss.mm"
include "cplusg.mm"
include "c0g.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cv.mm"
include "chdma.mm"
include "cmpt2.mm"
include "chg.mm"
include "cip.mm"
include "cocv.mm"
include "eqid.mm"
include "hlhilhillem.mm"

theorem hlathil
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilphl.h: |- H = ( LHyp ` K )
  assume hlhilphllem.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilphl.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> U e. Hil )

  proof
    wph
    vx
    vy
    cW
    cK
    cdvh
    cfv
    cfv
    #
    csca
    cfv
    #
    cbs
    cfv
    #
    cU
    ccss
    cfv
    #
    @0
    cplusg
    cfv
    #
    @1
    cplusg
    cfv
    #
    @1
    c0g
    cfv
    #
    @1
    @0
    cvsca
    cfv
    #
    @1
    cmulr
    cfv
    #
    cU
    vx
    vy
    @0
    cbs
    cfv
    #
    @9
    vx
    cv
    vy
    cv
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    cfv
    cmpt2
    #
    cU
    csca
    cfv
    #
    cW
    cK
    chg
    cfv
    cfv
    #
    cH
    cU
    cip
    cfv
    #
    @10
    cK
    @0
    cU
    cocv
    cfv
    #
    @9
    cW
    @0
    c0g
    cfv
    #
    hlhilphl.h
    hlhilphllem.u
    hlhilphl.k
    @12
    eqid
    @0
    eqid
    @9
    eqid
    @4
    eqid
    @7
    eqid
    @1
    eqid
    @2
    eqid
    @5
    eqid
    @8
    eqid
    @6
    eqid
    @16
    eqid
    @14
    eqid
    @10
    eqid
    @13
    eqid
    @11
    eqid
    @15
    eqid
    @3
    eqid
    hlhilhillem
end
