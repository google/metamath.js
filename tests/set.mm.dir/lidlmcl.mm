include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cvsca.mm"
include "cmulr.mm"
include "rlmvsca.mm"
include "eqtri.mm"
include "oveqi.mm"
include "clmod.mm"
include "clss.mm"
include "csca.mm"
include "cbs.mm"
include "rlmlmod.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "rlmsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "eqid.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "syl5eqel.mm"

theorem lidlmcl
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidlcl.b: |- B = ( Base ` R )
  assume lidlmcl.t: |- .x. = ( .r ` R )


  assert |- ( ( ( R e. Ring /\ I e. U ) /\ ( X e. B /\ Y e. I ) ) -> ( X .x. Y ) e. I )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cI
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.x
    co
    cX
    cY
    cR
    crglmod
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cI
    c.x
    @8
    cX
    cY
    c.x
    cR
    cmulr
    cfv
    @8
    lidlmcl.t
    cR
    rlmvsca
    eqtri
    oveqi
    @6
    @7
    clmod
    wcel
    #
    cI
    @7
    clss
    cfv
    #
    wcel
    #
    cX
    @7
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @4
    @9
    cI
    wcel
    @0
    @10
    @1
    @5
    cR
    rlmlmod
    ad2antrr
    @2
    @12
    @5
    @2
    cI
    cU
    @11
    @0
    @1
    simpr
    cU
    cR
    clidl
    cfv
    @11
    lidlcl.u
    cR
    lidlval
    eqtri
    syl6eleq
    adantr
    @0
    @3
    @15
    @1
    @4
    @0
    @3
    @15
    @0
    cB
    @14
    cX
    @0
    cB
    cR
    cbs
    cfv
    @14
    lidlcl.b
    @0
    cR
    @13
    cbs
    cR
    crg
    rlmsca
    fveq2d
    syl5eq
    eleq2d
    biimpa
    ad2ant2r
    @2
    @3
    @4
    simprr
    @14
    @11
    @8
    cI
    @13
    @7
    cX
    cY
    @13
    eqid
    @8
    eqid
    @14
    eqid
    @11
    eqid
    lssvscl
    syl22anc
    syl5eqel
end
