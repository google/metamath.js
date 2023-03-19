include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cip.mm"
include "co.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "ipffval.mm"
include "csubg.mm"
include "wceq.mm"
include "clmod.mm"
include "phllmod.mm"
include "lsssubg.mm"
include "sylan.mm"
include "subgbas.mm"
include "syl.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "wss.mm"
include "subgss.mm"
include "resmpt2.mm"
include "syl2anc.mm"
include "ssipeq.mm"
include "adantl.mm"
include "oveqd.mm"
include "mpt2eq3dv.mm"
include "3eqtr4rd.mm"
include "syl5eq.mm"
include "a1i.mm"
include "reseq1d.mm"
include "eqtr4d.mm"

theorem phssip
  let cP: class P
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume phssip.x: |- X = ( W |`s U )
  assume phssip.s: |- S = ( LSubSp ` W )
  assume phssip.i: |- .x. = ( .if ` W )
  assume phssip.p: |- P = ( .if ` X )


  assert |- ( ( W e. PreHil /\ U e. S ) -> P = ( .x. |` ( U X. U ) ) )

  proof
    cW
    cphl
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cP
    vx
    vy
    cW
    cbs
    cfv
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    cW
    cip
    cfv
    #
    co
    #
    cmpt2
    #
    cU
    cU
    cxp
    #
    cres
    #
    c.x
    @9
    cres
    @2
    cP
    vx
    vy
    cX
    cbs
    cfv
    #
    @11
    @4
    @5
    cX
    cip
    cfv
    #
    co
    #
    cmpt2
    #
    @10
    vx
    vy
    cP
    @12
    @11
    cX
    @11
    eqid
    @12
    eqid
    #
    phssip.p
    ipffval
    @2
    vx
    vy
    cU
    cU
    @7
    cmpt2
    #
    vx
    vy
    @11
    @11
    @7
    cmpt2
    @10
    @14
    @2
    vx
    vy
    cU
    cU
    @7
    @11
    @11
    @7
    @2
    cU
    cW
    csubg
    cfv
    wcel
    #
    cU
    @11
    wceq
    @0
    cW
    clmod
    wcel
    @1
    @17
    cW
    phllmod
    cS
    cU
    cW
    phssip.s
    lsssubg
    sylan
    #
    cU
    cW
    cX
    phssip.x
    subgbas
    syl
    #
    @19
    @2
    @7
    eqidd
    mpt2eq123dv
    @2
    cU
    @3
    wss
    #
    @20
    @10
    @16
    wceq
    @2
    @17
    @20
    @18
    @3
    cU
    cW
    @3
    eqid
    #
    subgss
    syl
    #
    @22
    vx
    vy
    @3
    @3
    cU
    cU
    @7
    resmpt2
    syl2anc
    @2
    vx
    vy
    @11
    @11
    @13
    @7
    @2
    @12
    @6
    @4
    @5
    @1
    @12
    @6
    wceq
    @0
    @12
    cS
    cU
    @6
    cW
    cX
    phssip.x
    @6
    eqid
    #
    @15
    ssipeq
    adantl
    oveqd
    mpt2eq3dv
    3eqtr4rd
    syl5eq
    @2
    c.x
    @8
    @9
    c.x
    @8
    wceq
    @2
    vx
    vy
    c.x
    @6
    @3
    cW
    @21
    @23
    phssip.i
    ipffval
    a1i
    reseq1d
    eqtr4d
end
