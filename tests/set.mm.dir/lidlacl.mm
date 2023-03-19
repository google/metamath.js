include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "eqtri.mm"
include "oveqi.mm"
include "clmod.mm"
include "clss.mm"
include "rlmlmod.mm"
include "adantr.mm"
include "simpr.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleq.mm"
include "jca.mm"
include "eqid.mm"
include "lssvacl.mm"
include "sylan.mm"
include "syl5eqel.mm"

theorem lidlacl
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidlacl.p: |- .+ = ( +g ` R )


  assert |- ( ( ( R e. Ring /\ I e. U ) /\ ( X e. I /\ Y e. I ) ) -> ( X .+ Y ) e. I )

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
    cI
    wcel
    cY
    cI
    wcel
    wa
    #
    wa
    cX
    cY
    c.pl
    co
    cX
    cY
    cR
    crglmod
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cI
    c.pl
    @5
    cX
    cY
    c.pl
    cR
    cplusg
    cfv
    @5
    lidlacl.p
    cR
    rlmplusg
    eqtri
    oveqi
    @2
    @4
    clmod
    wcel
    #
    cI
    @4
    clss
    cfv
    #
    wcel
    #
    wa
    @3
    @6
    cI
    wcel
    @2
    @7
    @9
    @0
    @7
    @1
    cR
    rlmlmod
    adantr
    @2
    cI
    cU
    @8
    @0
    @1
    simpr
    cU
    cR
    clidl
    cfv
    @8
    lidlcl.u
    cR
    lidlval
    eqtri
    syl6eleq
    jca
    @5
    @8
    cI
    @4
    cX
    cY
    @5
    eqid
    @8
    eqid
    lssvacl
    sylan
    syl5eqel
end
