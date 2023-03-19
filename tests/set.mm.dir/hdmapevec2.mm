include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wceq.mm"
include "csn.mm"
include "coch.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "hdmapevec.mm"
include "chlt.mm"
include "c0g.mm"
include "eqid.mm"
include "cltrn.mm"
include "dvheveccl.mm"
include "hvmapval.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "dochfl1.mm"

theorem hdmapevec2
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cH: class H
  let cJ: class J
  let cK: class K
  let cW: class W
  let vz: setvar z
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  assume hdmapevec.h: |- H = ( LHyp ` K )
  assume hdmapevec.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapevec.j: |- J = ( ( HVMap ` K ) ` W )
  assume hdmapevec.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapevec.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapevec2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapevec2.r: |- R = ( Scalar ` U )
  assume hdmapevec2.i: |- .1. = ( 1r ` R )


  assert |- ( ph -> ( ( S ` E ) ` E ) = .1. )

  proof
    wph
    cE
    cE
    cS
    cfv
    #
    cfv
    cE
    vv
    cU
    cbs
    cfv
    #
    vv
    cv
    vw
    cv
    vk
    cv
    cE
    cU
    cvsca
    cfv
    #
    co
    cU
    cplusg
    cfv
    #
    co
    wceq
    vw
    cE
    csn
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    wrex
    vk
    cR
    cbs
    cfv
    #
    crio
    cmpt
    #
    cfv
    c.1
    wph
    cE
    @0
    @6
    wph
    @0
    cE
    cJ
    cfv
    @6
    wph
    cS
    cE
    cH
    cJ
    cK
    cW
    hdmapevec.h
    hdmapevec.e
    hdmapevec.j
    hdmapevec.s
    hdmapevec.k
    hdmapevec
    wph
    vv
    vw
    chlt
    @3
    @5
    cR
    @2
    cU
    vk
    cH
    cK
    cJ
    @4
    @1
    cW
    cE
    cU
    c0g
    cfv
    #
    hdmapevec.h
    hdmapevec2.u
    @4
    eqid
    #
    @1
    eqid
    #
    @3
    eqid
    #
    @2
    eqid
    #
    @7
    eqid
    #
    hdmapevec2.r
    @5
    eqid
    #
    hdmapevec.j
    hdmapevec.k
    wph
    cK
    cbs
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cE
    cH
    cK
    @1
    cW
    @7
    hdmapevec.h
    @14
    eqid
    @15
    eqid
    hdmapevec2.u
    @9
    @12
    hdmapevec.e
    hdmapevec.k
    dvheveccl
    #
    hvmapval
    eqtrd
    fveq1d
    wph
    vw
    vv
    cR
    @3
    @5
    @2
    cU
    c.1
    vk
    @6
    cH
    cK
    @4
    @1
    cW
    cE
    @7
    hdmapevec.h
    @8
    hdmapevec2.u
    @9
    @10
    @11
    @12
    hdmapevec2.r
    @13
    hdmapevec2.i
    hdmapevec.k
    @16
    @6
    eqid
    dochfl1
    eqtrd
end
