include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "crglmod.mm"
include "cminusg.mm"
include "rlmvneg.mm"
include "eqtri.mm"
include "fveq1i.mm"
include "clmod.mm"
include "clss.mm"
include "rlmlmod.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simpr.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleq.mm"
include "3adant3.mm"
include "simp3.mm"
include "eqid.mm"
include "lssvnegcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem lidlnegcl
  let cR: class R
  let cU: class U
  let cI: class I
  let cN: class N
  let cX: class X
  assume lidlcl.u: |- U = ( LIdeal ` R )
  assume lidlnegcl.n: |- N = ( invg ` R )


  assert |- ( ( R e. Ring /\ I e. U /\ X e. I ) -> ( N ` X ) e. I )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    cX
    cI
    wcel
    #
    w3a
    #
    cX
    cN
    cfv
    cX
    cR
    crglmod
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    cI
    cX
    cN
    @5
    cN
    cR
    cminusg
    cfv
    @5
    lidlnegcl.n
    cR
    rlmvneg
    eqtri
    fveq1i
    @3
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
    @2
    @6
    cI
    wcel
    @0
    @1
    @7
    @2
    cR
    rlmlmod
    3ad2ant1
    @0
    @1
    @9
    @2
    @0
    @1
    wa
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
    3adant3
    @0
    @1
    @2
    simp3
    @8
    cI
    @5
    @4
    cX
    @8
    eqid
    @5
    eqid
    lssvnegcl
    syl3anc
    syl5eqel
end
