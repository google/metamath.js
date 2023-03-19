include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "c0g.mm"
include "rlm0.mm"
include "eqtri.mm"
include "clmod.mm"
include "clss.mm"
include "rlmlmod.mm"
include "adantr.mm"
include "simpr.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleq.mm"
include "eqid.mm"
include "lss0cl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem lidl0cl
  let cR: class R
  let cU: class U
  let cI: class I
  let c.0: class .0.
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidl0cl.z: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ I e. U ) -> .0. e. I )

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
    c.0
    cR
    crglmod
    cfv
    #
    c0g
    cfv
    #
    cI
    c.0
    cR
    c0g
    cfv
    @4
    lidl0cl.z
    cR
    rlm0
    eqtri
    @2
    @3
    clmod
    wcel
    #
    cI
    @3
    clss
    cfv
    #
    wcel
    @4
    cI
    wcel
    @0
    @5
    @1
    cR
    rlmlmod
    adantr
    @2
    cI
    cU
    @6
    @0
    @1
    simpr
    cU
    cR
    clidl
    cfv
    @6
    lidlcl.u
    cR
    lidlval
    eqtri
    syl6eleq
    @6
    cI
    @3
    @4
    @4
    eqid
    @6
    eqid
    lss0cl
    syl2anc
    syl5eqel
end
