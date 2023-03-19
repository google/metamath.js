include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cdib.mm"
include "wn.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "wceq.mm"
include "cdic.mm"
include "clsm.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "fvex.mm"
include "riotaex.mm"
include "ifex.mm"
include "rgenw.mm"
include "a1i.mm"
include "eqid.mm"
include "mptfng.mm"
include "sylib.mm"
include "dihfval.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "dihlss.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem dihf11lem
  let cB: class B
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vq: setvar q
  let vu: setvar u
  assume dihf11.b: |- B = ( Base ` K )
  assume dihf11.h: |- H = ( LHyp ` K )
  assume dihf11.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihf11.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihf11.s: |- S = ( LSubSp ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> I : B --> S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    cB
    wfn
    #
    cI
    crn
    cS
    wss
    #
    cB
    cS
    cI
    wf
    @0
    @1
    vx
    cB
    vx
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    @3
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    vq
    cv
    #
    cW
    @4
    wbr
    wn
    @8
    @3
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    @3
    wceq
    wa
    vu
    cv
    @8
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    @10
    @6
    cfv
    cU
    clsm
    cfv
    #
    co
    wceq
    wi
    vq
    cK
    catm
    cfv
    #
    wral
    #
    vu
    cS
    crio
    #
    cif
    #
    cmpt
    #
    cB
    wfn
    #
    @0
    @17
    cvv
    wcel
    #
    vx
    cB
    wral
    #
    @19
    @21
    @0
    @20
    vx
    cB
    @5
    @7
    @16
    @3
    @6
    fvex
    @15
    vu
    cS
    riotaex
    ifex
    rgenw
    a1i
    vx
    cB
    @17
    @18
    @18
    eqid
    mptfng
    sylib
    @0
    cB
    cI
    @18
    vx
    vu
    @14
    cB
    @12
    @6
    @13
    cS
    cU
    cH
    cI
    @11
    cK
    @4
    @9
    chlt
    cW
    vq
    dihf11.b
    @4
    eqid
    @11
    eqid
    @9
    eqid
    @14
    eqid
    dihf11.h
    dihf11.i
    @6
    eqid
    @12
    eqid
    dihf11.u
    dihf11.s
    @13
    eqid
    dihfval
    fneq1d
    mpbird
    #
    @0
    @1
    vy
    cv
    #
    cI
    cfv
    cS
    wcel
    #
    vy
    cB
    wral
    @2
    @22
    @0
    @24
    vy
    cB
    cB
    cS
    cU
    cH
    cI
    cK
    cW
    @23
    dihf11.b
    dihf11.h
    dihf11.i
    dihf11.u
    dihf11.s
    dihlss
    ralrimiva
    vy
    cB
    cS
    cI
    fnfvrnss
    syl2anc
    cB
    cS
    cI
    df-f
    sylanbrc
end
