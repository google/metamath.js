include "crrext.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctopn.mm"
include "czlm.mm"
include "eqid.mm"
include "rrextdrg.mm"
include "rrextnrg.mm"
include "rrextnlm.mm"
include "rrextchr.mm"
include "rrextcusp.mm"
include "rrextust.mm"
include "rrhf.mm"

theorem rrhfe
  let cB: class B
  let cR: class R
  assume rrhfe.b: |- B = ( Base ` R )


  assert |- ( R e. RRExt -> ( RRHom ` R ) : RR --> B )

  proof
    cR
    crrext
    wcel
    cB
    cR
    cds
    cfv
    cB
    cB
    cxp
    cres
    #
    cR
    cioo
    crn
    ctg
    cfv
    #
    cR
    ctopn
    cfv
    #
    cR
    czlm
    cfv
    #
    @0
    eqid
    #
    @1
    eqid
    rrhfe.b
    @2
    eqid
    @3
    eqid
    #
    cR
    rrextdrg
    cR
    rrextnrg
    cR
    @3
    @5
    rrextnlm
    cR
    rrextchr
    cR
    rrextcusp
    cB
    @0
    cR
    rrhfe.b
    @4
    rrextust
    rrhf
end
