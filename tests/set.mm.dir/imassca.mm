include "csca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "cvsca.mm"
include "cv.mm"
include "csn.mm"
include "co.mm"
include "cmpt2.mm"
include "ciun.mm"
include "cip.mm"
include "cun.mm"
include "cts.mm"
include "ctopn.mm"
include "cqtop.mm"
include "cple.mm"
include "ccom.mm"
include "ccnv.mm"
include "cds.mm"
include "eqid.mm"
include "imasplusg.mm"
include "imasmulr.mm"
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "imasvalstr.mm"
include "scaid.mm"
include "snsstp1.mm"
include "ssun2.mm"
include "sstri.mm"
include "ssun1.mm"
include "strfv.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem imassca
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
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
  assume imassca.g: |- G = ( Scalar ` R )


  assert |- ( ph -> G = ( Scalar ` U ) )

  proof
    wph
    cU
    csca
    cfv
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
    #
    cnx
    csca
    cfv
    cG
    cop
    #
    cnx
    cvsca
    cfv
    vq
    cV
    vp
    vx
    cG
    cbs
    cfv
    #
    vq
    cv
    #
    cF
    cfv
    #
    csn
    vp
    cv
    #
    @5
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
    #
    cnx
    cip
    cfv
    vp
    cV
    vq
    cV
    @7
    cF
    cfv
    @6
    cop
    @7
    @5
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
    #
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
    cU
    cds
    cfv
    #
    cop
    ctp
    #
    cun
    #
    csca
    cfv
    #
    cG
    wph
    cU
    @22
    csca
    wph
    vx
    vy
    cB
    @20
    cR
    cplusg
    cfv
    #
    @0
    cR
    @1
    @8
    cR
    cmulr
    cfv
    #
    @9
    cU
    vg
    vh
    vi
    vn
    cR
    cds
    cfv
    #
    cF
    cG
    @11
    @12
    @16
    @4
    @19
    @18
    @17
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    @24
    eqid
    #
    @25
    eqid
    #
    imassca.g
    @4
    eqid
    @8
    eqid
    @11
    eqid
    @16
    eqid
    @26
    eqid
    #
    @18
    eqid
    wph
    cB
    @24
    @0
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
    @27
    @0
    eqid
    imasplusg
    wph
    cB
    cR
    @1
    @25
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
    @28
    @1
    eqid
    imasmulr
    wph
    @9
    eqidd
    wph
    @12
    eqidd
    wph
    @17
    eqidd
    wph
    vx
    vy
    cB
    @20
    cR
    cU
    vg
    vh
    vi
    vn
    @26
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @29
    @20
    eqid
    imasds
    wph
    @19
    eqidd
    imasbas.f
    imasbas.r
    imasval
    fveq2d
    cG
    cvv
    wcel
    cG
    @23
    wceq
    cG
    cR
    csca
    cfv
    cvv
    imassca.g
    cR
    csca
    fvex
    eqeltri
    cG
    @22
    csca
    cvv
    c1
    c1
    c2
    cdc
    cop
    cB
    @20
    @0
    cG
    @9
    @1
    @22
    @12
    @19
    @17
    @22
    eqid
    imasvalstr
    scaid
    @3
    csn
    #
    @15
    @22
    @30
    @14
    @15
    @3
    @10
    @13
    snsstp1
    @14
    @2
    ssun2
    sstri
    @15
    @21
    ssun1
    sstri
    strfv
    ax-mp
    syl6reqr
end
