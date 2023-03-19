include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctendo.mm"
include "copab.mm"
include "cxp.mm"
include "simprl.mm"
include "simpll.mm"
include "simprr.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendocl.mm"
include "eqeltrd.mm"
include "jca31.mm"
include "ex.mm"
include "ssopab2dv.mm"
include "opabssxp.mm"
include "syl6ss.mm"
include "dicval.mm"
include "dvhvbase.mm"
include "adantr.mm"
include "3sstr4d.mm"

theorem dicssdvh
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vs: setvar s
  assume dicssdvh.l: |- .<_ = ( le ` K )
  assume dicssdvh.a: |- A = ( Atoms ` K )
  assume dicssdvh.h: |- H = ( LHyp ` K )
  assume dicssdvh.i: |- I = ( ( DIsoC ` K ) ` W )
  assume dicssdvh.u: |- U = ( ( DVecH ` K ) ` W )
  assume dicssdvh.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) C_ V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    vf
    cv
    #
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vg
    cv
    cfv
    cQ
    wceq
    vg
    cW
    cK
    cltrn
    cfv
    cfv
    #
    crio
    #
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @8
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    wa
    #
    vf
    vs
    copab
    #
    @6
    @11
    cxp
    #
    cQ
    cI
    cfv
    cV
    @2
    @14
    @3
    @6
    wcel
    #
    @12
    wa
    @12
    wa
    #
    vf
    vs
    copab
    @15
    @2
    @13
    @17
    vf
    vs
    @2
    @13
    @17
    @2
    @13
    wa
    #
    @16
    @12
    @12
    @18
    @3
    @9
    @6
    @2
    @10
    @12
    simprl
    @18
    @0
    @12
    @7
    @6
    wcel
    #
    @9
    @6
    wcel
    @0
    @1
    @13
    simpll
    #
    @2
    @10
    @12
    simprr
    #
    @18
    @0
    @5
    cA
    wcel
    @5
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @19
    @20
    @0
    @22
    @1
    @13
    cA
    cH
    cK
    c.le
    @4
    cW
    dicssdvh.l
    @4
    eqid
    dicssdvh.a
    dicssdvh.h
    lhpocnel
    ad2antrr
    @0
    @1
    @13
    simplr
    cA
    @5
    cQ
    @6
    vg
    @7
    cH
    cK
    c.le
    cW
    dicssdvh.l
    dicssdvh.a
    dicssdvh.h
    @6
    eqid
    #
    @7
    eqid
    ltrniotacl
    syl3anc
    @8
    @6
    @11
    @7
    cH
    cK
    chlt
    cW
    dicssdvh.h
    @23
    @11
    eqid
    #
    tendocl
    syl3anc
    eqeltrd
    @21
    @21
    jca31
    ex
    ssopab2dv
    @12
    vf
    vs
    @6
    @11
    opabssxp
    syl6ss
    cA
    @5
    cQ
    @6
    vf
    vg
    @11
    cH
    cI
    cK
    c.le
    chlt
    cW
    vs
    dicssdvh.l
    dicssdvh.a
    dicssdvh.h
    @5
    eqid
    @23
    @24
    dicssdvh.i
    dicval
    @0
    cV
    @15
    wceq
    @1
    @6
    cU
    @11
    cH
    cK
    cV
    cW
    chlt
    dicssdvh.h
    @23
    @24
    dicssdvh.u
    dicssdvh.v
    dvhvbase
    adantr
    3sstr4d
end
