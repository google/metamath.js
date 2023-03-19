include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "ciedg.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c2nd.mm"
include "cedgf.mm"
include "cif.mm"
include "iedgval.mm"
include "fundmge2nop0.mm"
include "iffalsed.mm"
include "syl5eq.mm"

theorem funiedgdmge2val
  let cG: class G


  assert |- ( ( Fun ( G \ { (/) } ) /\ 2 <_ ( # ` dom G ) ) -> ( iEdg ` G ) = ( .ef ` G ) )

  proof
    cG
    c0
    csn
    cdif
    wfun
    c2
    cG
    cdm
    chash
    cfv
    cle
    wbr
    wa
    #
    cG
    ciedg
    cfv
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    c2nd
    cfv
    #
    cG
    cedgf
    cfv
    #
    cif
    @3
    cG
    iedgval
    @0
    @1
    @2
    @3
    cG
    fundmge2nop0
    iffalsed
    syl5eq
end
