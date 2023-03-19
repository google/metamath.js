include "cxp.mm"
include "wfn.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cmap.mm"
include "crab.mm"
include "cxrs.mm"
include "ccom.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt2.mm"
include "eqid.mm"
include "xrltso.mm"
include "infex.mm"
include "fnmpt2i.mm"
include "imasds.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem imasdsfn
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cK: class K
  let cS: class S
  let cY: class Y
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )
  assume imasds.e: |- E = ( dist ` R )
  assume imasds.d: |- D = ( dist ` U )


  assert |- ( ph -> D Fn ( B X. B ) )

  proof
    wph
    cD
    cB
    cB
    cxp
    #
    wfn
    vx
    vy
    cB
    cB
    vn
    cn
    vg
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    cF
    cfv
    vx
    cv
    wceq
    vn
    cv
    #
    @1
    cfv
    c2nd
    cfv
    cF
    cfv
    vy
    cv
    wceq
    vi
    cv
    #
    @1
    cfv
    c2nd
    cfv
    cF
    cfv
    @3
    c1
    caddc
    co
    @1
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @2
    c1
    cmin
    co
    cfz
    co
    wral
    w3a
    vh
    cV
    cV
    cxp
    c1
    @2
    cfz
    co
    cmap
    co
    crab
    cxrs
    cE
    vg
    cv
    ccom
    cgsu
    co
    cmpt
    crn
    ciun
    #
    cxr
    clt
    cinf
    #
    cmpt2
    #
    @0
    wfn
    vx
    vy
    cB
    cB
    @5
    @6
    @6
    eqid
    cxr
    @4
    clt
    xrltso
    infex
    fnmpt2i
    wph
    @0
    cD
    @6
    wph
    vx
    vy
    cB
    cD
    cR
    cU
    vg
    vh
    vi
    vn
    cE
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    imasds.e
    imasds.d
    imasds
    fneq1d
    mpbiri
end
