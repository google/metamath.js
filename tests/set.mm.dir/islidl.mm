include "cid.mm"
include "cfv.mm"
include "crglmod.mm"
include "rlmsca2.mm"
include "cbs.mm"
include "cnx.mm"
include "baseid.mm"
include "strfvi.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "cplusg.mm"
include "rlmplusg.mm"
include "cmulr.mm"
include "cvsca.mm"
include "rlmvsca.mm"
include "clidl.mm"
include "clss.mm"
include "lidlval.mm"
include "islss.mm"

theorem islidl
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let va: setvar a
  let vb: setvar b
  assume islidl.s: |- U = ( LIdeal ` R )
  assume islidl.b: |- B = ( Base ` R )
  assume islidl.p: |- .+ = ( +g ` R )
  assume islidl.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint I a
  disjoint I b
  disjoint I x
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint R a
  disjoint R b
  disjoint R x
  assert |- ( I e. U <-> ( I C_ B /\ I =/= (/) /\ A. x e. B A. a e. I A. b e. I ( ( x .x. a ) .+ b ) e. I ) )

  proof
    vx
    cB
    c.pl
    cU
    c.x
    cI
    cR
    cid
    cfv
    cB
    cR
    crglmod
    cfv
    #
    va
    vb
    cR
    rlmsca2
    cR
    cbs
    cnx
    cbs
    cfv
    cB
    baseid
    islidl.b
    strfvi
    cB
    cR
    cbs
    cfv
    @0
    cbs
    cfv
    islidl.b
    cR
    rlmbas
    eqtri
    c.pl
    cR
    cplusg
    cfv
    @0
    cplusg
    cfv
    islidl.p
    cR
    rlmplusg
    eqtri
    c.x
    cR
    cmulr
    cfv
    @0
    cvsca
    cfv
    islidl.t
    cR
    rlmvsca
    eqtri
    cU
    cR
    clidl
    cfv
    @0
    clss
    cfv
    islidl.s
    cR
    lidlval
    eqtri
    islss
end
