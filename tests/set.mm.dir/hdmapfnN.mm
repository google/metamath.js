include "wfn.mm"
include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "csn.mm"
include "clspn.mm"
include "cun.mm"
include "wcel.mm"
include "wn.mm"
include "chvm.mm"
include "cotp.mm"
include "chdma1.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "clcd.mm"
include "crio.mm"
include "cmpt.mm"
include "riotaex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "chlt.mm"
include "hdmapfval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem hdmapfnN
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vt: setvar t
  let vy: setvar y
  let vz: setvar z
  assume hdmapfn.h: |- H = ( LHyp ` K )
  assume hdmapfn.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapfn.v: |- V = ( Base ` U )
  assume hdmapfn.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapfn.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> S Fn V )

  proof
    wph
    cS
    cV
    wfn
    vt
    cV
    vz
    cv
    #
    cid
    cK
    cbs
    cfv
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    cres
    cop
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    vt
    cv
    #
    csn
    @2
    cfv
    cun
    wcel
    wn
    vy
    cv
    @0
    @1
    @1
    cW
    cK
    chvm
    cfv
    cfv
    #
    cfv
    @0
    cotp
    cW
    cK
    chdma1
    cfv
    cfv
    #
    cfv
    @3
    cotp
    @5
    cfv
    wceq
    wi
    vz
    cV
    wral
    #
    vy
    cW
    cK
    clcd
    cfv
    cfv
    #
    cbs
    cfv
    #
    crio
    #
    cmpt
    #
    cV
    wfn
    vt
    cV
    @9
    @10
    @6
    vy
    @8
    riotaex
    @10
    eqid
    fnmpti
    wph
    cV
    cS
    @10
    wph
    vy
    vz
    vt
    chlt
    @7
    @8
    cS
    cU
    @1
    cH
    @5
    @4
    cK
    @2
    cV
    cW
    hdmapfn.h
    @1
    eqid
    hdmapfn.u
    hdmapfn.v
    @2
    eqid
    @7
    eqid
    @8
    eqid
    @4
    eqid
    @5
    eqid
    hdmapfn.s
    hdmapfn.k
    hdmapfval
    fneq1d
    mpbiri
end
