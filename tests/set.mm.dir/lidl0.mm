include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "crglmod.mm"
include "cfv.mm"
include "clss.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "c0g.mm"
include "rlm0.mm"
include "eqtri.mm"
include "eqid.mm"
include "lsssn0.mm"
include "syl.mm"
include "clidl.mm"
include "lidlval.mm"
include "syl6eleqr.mm"

theorem lidl0
  let cR: class R
  let cU: class U
  let c.0: class .0.
  assume lidl0.u: |- U = ( LIdeal ` R )
  assume lidl0.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> { .0. } e. U )

  proof
    cR
    crg
    wcel
    #
    c.0
    csn
    #
    cR
    crglmod
    cfv
    #
    clss
    cfv
    #
    cU
    @0
    @2
    clmod
    wcel
    @1
    @3
    wcel
    cR
    rlmlmod
    @3
    @2
    c.0
    c.0
    cR
    c0g
    cfv
    @2
    c0g
    cfv
    lidl0.z
    cR
    rlm0
    eqtri
    @3
    eqid
    lsssn0
    syl
    cU
    cR
    clidl
    cfv
    @3
    lidl0.u
    cR
    lidlval
    eqtri
    syl6eleqr
end
