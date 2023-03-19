include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "ciun.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cmpt2.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "ctopn.mm"
include "cqtop.mm"
include "cple.mm"
include "ccom.mm"
include "ccnv.mm"
include "cds.mm"
include "cn.mm"
include "c1.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "cxrs.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cvv.mm"
include "c2.mm"
include "cdc.mm"
include "eqid.mm"
include "eqidd.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "baseid.mm"
include "snsstp1.mm"
include "ssun1.mm"
include "sstri.mm"
include "wcel.mm"
include "wfo.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "fornex.mm"
include "sylc.mm"
include "strfv3.mm"
include "eqcomd.mm"

theorem imasbas
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
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
  let cE: class E
  let cX: class X
  let cK: class K
  let cS: class S
  let cY: class Y
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )


  assert |- ( ph -> B = ( Base ` U ) )

  proof
    wph
    cU
    cbs
    cfv
    #
    cB
    wph
    @0
    cB
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    cplusg
    cfv
    vp
    cV
    vq
    cV
    vp
    cv
    #
    cF
    cfv
    vq
    cv
    #
    cF
    cfv
    #
    cop
    #
    @2
    @3
    cR
    cplusg
    cfv
    #
    co
    cF
    cfv
    cop
    csn
    ciun
    ciun
    #
    cop
    #
    cnx
    cmulr
    cfv
    vp
    cV
    vq
    cV
    @5
    @2
    @3
    cR
    cmulr
    cfv
    #
    co
    cF
    cfv
    cop
    csn
    ciun
    ciun
    #
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    cR
    csca
    cfv
    #
    cop
    cnx
    cvsca
    cfv
    vq
    cV
    vp
    vx
    @13
    cbs
    cfv
    #
    @4
    csn
    @2
    @3
    cR
    cvsca
    cfv
    #
    co
    cF
    cfv
    cmpt2
    ciun
    #
    cop
    cnx
    cip
    cfv
    vp
    cV
    vq
    cV
    @5
    @2
    @3
    cR
    cip
    cfv
    #
    co
    cop
    csn
    ciun
    ciun
    #
    cop
    ctp
    #
    cun
    #
    cnx
    cts
    cfv
    cR
    ctopn
    cfv
    #
    cF
    cqtop
    co
    #
    cop
    cnx
    cple
    cfv
    cF
    cR
    cple
    cfv
    #
    ccom
    cF
    ccnv
    ccom
    #
    cop
    cnx
    cds
    cfv
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
    @25
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
    @25
    cfv
    c2nd
    cfv
    cF
    cfv
    @27
    c1
    caddc
    co
    @25
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @26
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
    @26
    cfz
    co
    cmap
    co
    crab
    cxrs
    cR
    cds
    cfv
    #
    vg
    cv
    ccom
    cgsu
    co
    cmpt
    crn
    ciun
    cxr
    clt
    cinf
    cmpt2
    #
    cop
    ctp
    #
    cun
    #
    cU
    cbs
    cvv
    c1
    c1
    c2
    cdc
    cop
    wph
    vx
    vy
    cB
    @29
    @6
    @7
    cR
    @10
    @15
    @9
    @16
    cU
    vg
    vh
    vi
    vn
    @28
    cF
    @13
    @17
    @18
    @21
    @14
    @24
    @23
    @22
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @6
    eqid
    @9
    eqid
    @13
    eqid
    @14
    eqid
    @15
    eqid
    @17
    eqid
    @21
    eqid
    @28
    eqid
    @23
    eqid
    wph
    @7
    eqidd
    wph
    @10
    eqidd
    wph
    @16
    eqidd
    wph
    @18
    eqidd
    wph
    @22
    eqidd
    wph
    @29
    eqidd
    wph
    @24
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @29
    @7
    @13
    @16
    @10
    @31
    @18
    @24
    @22
    @31
    eqid
    imasvalstr
    baseid
    @1
    csn
    #
    @20
    @31
    @32
    @12
    @20
    @1
    @8
    @11
    snsstp1
    @12
    @19
    ssun1
    sstri
    @20
    @30
    ssun1
    sstri
    wph
    cV
    cvv
    wcel
    cV
    cB
    cF
    wfo
    cB
    cvv
    wcel
    wph
    cV
    cR
    cbs
    cfv
    cvv
    imasbas.v
    cR
    cbs
    fvex
    syl6eqel
    imasbas.f
    cV
    cB
    cvv
    cF
    fornex
    sylc
    @0
    eqid
    strfv3
    eqcomd
end
