include "ccom.mm"
include "ccnv.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cip.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "ciun.mm"
include "cun.mm"
include "cts.mm"
include "cple.mm"
include "cds.mm"
include "cvv.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "ctopn.mm"
include "eqid.mm"
include "imasplusg.mm"
include "imasmulr.mm"
include "imasvsca.mm"
include "eqidd.mm"
include "imastset.mm"
include "imasds.mm"
include "imasval.mm"
include "imasvalstr.mm"
include "pleid.mm"
include "snsstp2.mm"
include "ssun2.mm"
include "sstri.mm"
include "wcel.mm"
include "wf.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "fex.mm"
include "syl2anc.mm"
include "eqeltri.mm"
include "coexg.mm"
include "sylancl.mm"
include "cnvexg.mm"
include "strfv3.mm"

theorem imasle
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let c.le: class .<_
  let cN: class N
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
  assume imasle.n: |- N = ( le ` R )
  assume imasle.l: |- .<_ = ( le ` U )


  assert |- ( ph -> .<_ = ( ( F o. N ) o. `' F ) )

  proof
    wph
    c.le
    cF
    cN
    ccom
    #
    cF
    ccnv
    #
    ccom
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    cU
    cplusg
    cfv
    #
    cop
    cnx
    cmulr
    cfv
    cU
    cmulr
    cfv
    #
    cop
    ctp
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
    cU
    cvsca
    cfv
    #
    cop
    cnx
    cip
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
    cop
    @7
    @8
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
    cun
    #
    cnx
    cts
    cfv
    cU
    cts
    cfv
    #
    cop
    #
    cnx
    cple
    cfv
    @2
    cop
    #
    cnx
    cds
    cfv
    cU
    cds
    cfv
    #
    cop
    #
    ctp
    #
    cun
    #
    cU
    cple
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
    @15
    cR
    cplusg
    cfv
    #
    @3
    cR
    @4
    cR
    cvsca
    cfv
    #
    cR
    cmulr
    cfv
    #
    @6
    cU
    vz
    vw
    vv
    vu
    cR
    cds
    cfv
    #
    cF
    @5
    @9
    @10
    cR
    ctopn
    cfv
    #
    @5
    cbs
    cfv
    #
    @2
    cN
    @12
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @19
    eqid
    #
    @21
    eqid
    #
    @5
    eqid
    #
    @24
    eqid
    #
    @20
    eqid
    #
    @9
    eqid
    @23
    eqid
    #
    @22
    eqid
    #
    imasle.n
    wph
    cB
    @19
    @3
    cR
    cU
    cF
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @25
    @3
    eqid
    imasplusg
    wph
    cB
    cR
    @4
    @21
    cU
    cF
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @26
    @4
    eqid
    imasmulr
    wph
    vx
    cB
    cR
    @6
    @20
    cU
    cF
    @5
    @24
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @27
    @28
    @29
    @6
    eqid
    imasvsca
    wph
    @10
    eqidd
    wph
    cB
    cR
    cU
    cF
    @23
    @12
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @30
    @12
    eqid
    imastset
    wph
    vx
    vy
    cB
    @15
    cR
    cU
    vz
    vw
    vv
    vu
    @22
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @31
    @15
    eqid
    imasds
    wph
    @2
    eqidd
    imasbas.f
    imasbas.r
    imasval
    cB
    @15
    @3
    @5
    @6
    @4
    @18
    @10
    @2
    @12
    @18
    eqid
    imasvalstr
    pleid
    @14
    csn
    @17
    @18
    @13
    @14
    @16
    snsstp2
    @17
    @11
    ssun2
    sstri
    wph
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    wph
    cF
    cvv
    wcel
    #
    cN
    cvv
    wcel
    @32
    wph
    cV
    cB
    cF
    wf
    #
    cV
    cvv
    wcel
    @34
    wph
    cV
    cB
    cF
    wfo
    @35
    imasbas.f
    cV
    cB
    cF
    fof
    syl
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
    cV
    cB
    cvv
    cF
    fex
    syl2anc
    #
    cN
    cR
    cple
    cfv
    cvv
    imasle.n
    cR
    cple
    fvex
    eqeltri
    cF
    cN
    cvv
    cvv
    coexg
    sylancl
    wph
    @34
    @33
    @36
    cF
    cvv
    cnvexg
    syl
    @0
    @1
    cvv
    cvv
    coexg
    syl2anc
    imasle.l
    strfv3
end
