include "crrext.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "czlm.mm"
include "eqid.mm"
include "rrextdrg.mm"
include "rrextnrg.mm"
include "rrextnlm.mm"
include "rrextchr.mm"
include "rrextcusp.mm"
include "rrextust.mm"
include "rrhcn.mm"

theorem rrhcne
  let cR: class R
  let cJ: class J
  let cK: class K
  assume rrhcne.j: |- J = ( topGen ` ran (,) )
  assume rrhcne.k: |- K = ( TopOpen ` R )


  assert |- ( R e. RRExt -> ( RRHom ` R ) e. ( J Cn K ) )

  proof
    cR
    crrext
    wcel
    cR
    cbs
    cfv
    #
    cR
    cds
    cfv
    @0
    @0
    cxp
    cres
    #
    cR
    cJ
    cK
    cR
    czlm
    cfv
    #
    @1
    eqid
    #
    rrhcne.j
    @0
    eqid
    #
    rrhcne.k
    @2
    eqid
    #
    cR
    rrextdrg
    cR
    rrextnrg
    cR
    @2
    @5
    rrextnlm
    cR
    rrextchr
    cR
    rrextcusp
    @0
    @1
    cR
    @4
    @3
    rrextust
    rrhcn
end
