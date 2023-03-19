include "crg.mm"
include "wcel.mm"
include "crglmod.mm"
include "cfv.mm"
include "clmod.mm"
include "csn.mm"
include "wceq.mm"
include "rlmlmod.mm"
include "c0g.mm"
include "rlm0.mm"
include "eqtri.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "lspsn0.mm"
include "syl.mm"

theorem rsp0
  let cR: class R
  let cK: class K
  let c.0: class .0.
  assume rspcl.k: |- K = ( RSpan ` R )
  assume rsp0.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( K ` { .0. } ) = { .0. } )

  proof
    cR
    crg
    wcel
    cR
    crglmod
    cfv
    #
    clmod
    wcel
    c.0
    csn
    #
    cK
    cfv
    @1
    wceq
    cR
    rlmlmod
    cK
    @0
    c.0
    c.0
    cR
    c0g
    cfv
    @0
    c0g
    cfv
    rsp0.z
    cR
    rlm0
    eqtri
    cK
    cR
    crsp
    cfv
    @0
    clspn
    cfv
    rspcl.k
    cR
    rspval
    eqtri
    lspsn0
    syl
end
