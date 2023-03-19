include "cdvh.mm"
include "cfv.mm"
include "clvec.mm"
include "wcel.mm"
include "eqid.mm"
include "dvhlvec.mm"
include "cbs.mm"
include "csca.mm"
include "eqidd.mm"
include "hlhilbase.mm"
include "hlhilsbase2.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "hlhilplus.mm"
include "oveqdr.mm"
include "hlhilsplus2.mm"
include "cmulr.mm"
include "hlhilsmul2.mm"
include "cvsca.mm"
include "hlhilvsca.mm"
include "lvecprop2d.mm"
include "mpbid.mm"

theorem hlhillvec
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  assume hlhillvec.h: |- H = ( LHyp ` K )
  assume hlhillvec.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhillvec.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> U e. LVec )

  proof
    wph
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clvec
    wcel
    cU
    clvec
    wcel
    wph
    @0
    cH
    cK
    cW
    hlhillvec.h
    @0
    eqid
    #
    hlhillvec.k
    dvhlvec
    wph
    vx
    vy
    @0
    cbs
    cfv
    #
    @0
    csca
    cfv
    #
    cbs
    cfv
    #
    @3
    cU
    csca
    cfv
    #
    @0
    cU
    wph
    @2
    eqidd
    wph
    cU
    cH
    cK
    @0
    @2
    cW
    hlhillvec.h
    hlhillvec.u
    hlhillvec.k
    @1
    @2
    eqid
    hlhilbase
    @3
    eqid
    #
    @5
    eqid
    #
    wph
    @4
    eqidd
    wph
    @4
    @5
    @3
    cU
    cH
    cK
    @0
    cW
    hlhillvec.h
    @1
    @6
    hlhillvec.u
    @7
    hlhillvec.k
    @4
    eqid
    hlhilsbase2
    wph
    vx
    cv
    #
    @2
    wcel
    vy
    cv
    #
    @2
    wcel
    #
    wa
    vx
    vy
    @0
    cplusg
    cfv
    #
    cU
    cplusg
    cfv
    wph
    @11
    cU
    cH
    cK
    @0
    cW
    hlhillvec.h
    hlhillvec.u
    hlhillvec.k
    @1
    @11
    eqid
    hlhilplus
    oveqdr
    wph
    @8
    @4
    wcel
    #
    @9
    @4
    wcel
    wa
    #
    vx
    vy
    @3
    cplusg
    cfv
    #
    @5
    cplusg
    cfv
    wph
    @14
    @5
    @3
    cU
    cH
    cK
    @0
    cW
    hlhillvec.h
    @1
    @6
    hlhillvec.u
    @7
    hlhillvec.k
    @14
    eqid
    hlhilsplus2
    oveqdr
    wph
    @13
    vx
    vy
    @3
    cmulr
    cfv
    #
    @5
    cmulr
    cfv
    wph
    @5
    @3
    @15
    cU
    cH
    cK
    @0
    cW
    hlhillvec.h
    @1
    @6
    hlhillvec.u
    @7
    hlhillvec.k
    @15
    eqid
    hlhilsmul2
    oveqdr
    wph
    @12
    @10
    wa
    vx
    vy
    @0
    cvsca
    cfv
    #
    cU
    cvsca
    cfv
    wph
    @16
    cU
    cH
    cK
    @0
    cW
    hlhillvec.h
    @1
    @16
    eqid
    hlhillvec.u
    hlhillvec.k
    hlhilvsca
    oveqdr
    lvecprop2d
    mpbid
end
