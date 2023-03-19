include "wfn.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "chdma.mm"
include "clcd.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "crio.mm"
include "cmpt.mm"
include "riotaex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "chlt.mm"
include "hgmapfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem hgmapfnN
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume hgmapfn.h: |- H = ( LHyp ` K )
  assume hgmapfn.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapfn.r: |- R = ( Scalar ` U )
  assume hgmapfn.b: |- B = ( Base ` R )
  assume hgmapfn.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapfn.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> G Fn B )

  proof
    wph
    cG
    cB
    wfn
    vk
    cB
    vk
    cv
    vx
    cv
    #
    cU
    cvsca
    cfv
    #
    co
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    vj
    cv
    @0
    @2
    cfv
    cW
    cK
    clcd
    cfv
    cfv
    #
    cvsca
    cfv
    #
    co
    wceq
    vx
    cU
    cbs
    cfv
    #
    wral
    #
    vj
    cB
    crio
    #
    cmpt
    #
    cB
    wfn
    vk
    cB
    @7
    @8
    @6
    vj
    cB
    riotaex
    @8
    eqid
    fnmpti
    wph
    cB
    cG
    @8
    wph
    vk
    vj
    vx
    cB
    @3
    cR
    @4
    @1
    cU
    cH
    cG
    cK
    @2
    @5
    cW
    chlt
    hgmapfn.h
    hgmapfn.u
    @5
    eqid
    @1
    eqid
    hgmapfn.r
    hgmapfn.b
    @3
    eqid
    @4
    eqid
    @2
    eqid
    hgmapfn.g
    hgmapfn.k
    hgmapfval
    fneq1d
    mpbiri
end
