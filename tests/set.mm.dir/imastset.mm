include "cts.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
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
include "cqtop.mm"
include "cple.mm"
include "ccom.mm"
include "ccnv.mm"
include "cds.mm"
include "eqid.mm"
include "imasplusg.mm"
include "imasmulr.mm"
include "imasvsca.mm"
include "eqidd.mm"
include "imasds.mm"
include "imasval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "imasvalstr.mm"
include "tsetid.mm"
include "snsstp1.mm"
include "ssun2.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem imastset
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cJ: class J
  let cO: class O
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
  assume imastset.j: |- J = ( TopOpen ` R )
  assume imastset.o: |- O = ( TopSet ` U )


  assert |- ( ph -> O = ( J qTop F ) )

  proof
    wph
    cU
    cts
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
    @4
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
    ctp
    cun
    #
    cnx
    cts
    cfv
    cJ
    cF
    cqtop
    co
    #
    cop
    #
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
    cts
    cfv
    #
    cO
    @9
    wph
    cU
    @17
    cts
    wph
    vx
    vy
    cB
    @14
    cR
    cplusg
    cfv
    #
    @0
    cR
    @1
    cR
    cvsca
    cfv
    #
    cR
    cmulr
    cfv
    #
    @3
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
    @2
    @6
    @7
    cJ
    @2
    cbs
    cfv
    #
    @12
    @11
    @9
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
    @2
    eqid
    #
    @23
    eqid
    #
    @20
    eqid
    #
    @6
    eqid
    imastset.j
    @22
    eqid
    #
    @11
    eqid
    wph
    cB
    @19
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
    @24
    @0
    eqid
    imasplusg
    wph
    cB
    cR
    @1
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
    @25
    @1
    eqid
    imasmulr
    wph
    vx
    cB
    cR
    @3
    @20
    cU
    cF
    @2
    @23
    cV
    cZ
    vq
    vp
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    @26
    @27
    @28
    @3
    eqid
    imasvsca
    wph
    @7
    eqidd
    wph
    @9
    eqidd
    wph
    vx
    vy
    cB
    @14
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
    @29
    @14
    eqid
    imasds
    wph
    @12
    eqidd
    imasbas.f
    imasbas.r
    imasval
    fveq2d
    imastset.o
    @9
    cvv
    wcel
    @9
    @18
    wceq
    cJ
    cF
    cqtop
    ovex
    @9
    @17
    cts
    cvv
    c1
    c1
    c2
    cdc
    cop
    cB
    @14
    @0
    @2
    @3
    @1
    @17
    @7
    @12
    @9
    @17
    eqid
    imasvalstr
    tsetid
    @10
    csn
    @16
    @17
    @10
    @13
    @15
    snsstp1
    @16
    @8
    ssun2
    sstri
    strfv
    ax-mp
    3eqtr4g
end
