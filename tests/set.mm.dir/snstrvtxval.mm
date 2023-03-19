include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "wne.mm"
include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "c1st.mm"
include "cif.mm"
include "cvtx.mm"
include "wn.mm"
include "necom.mm"
include "fvex.mm"
include "funsndifnop.mm"
include "sylbi.mm"
include "iffalsed.mm"
include "wceq.mm"
include "vtxval.mm"
include "a1i.mm"
include "1strbas.mm"
include "mp1i.mm"
include "3eqtr4d.mm"

theorem snstrvtxval
  let cG: class G
  let cV: class V
  assume snstrvtxval.v: |- V e. _V
  assume snstrvtxval.g: |- G = { <. ( Base ` ndx ) , V >. }


  assert |- ( V =/= ( Base ` ndx ) -> ( Vtx ` G ) = V )

  proof
    cV
    cnx
    cbs
    cfv
    #
    wne
    #
    cG
    cvv
    cvv
    cxp
    wcel
    #
    cG
    c1st
    cfv
    #
    cG
    cbs
    cfv
    #
    cif
    #
    @4
    cG
    cvtx
    cfv
    #
    cV
    @1
    @2
    @3
    @4
    @1
    @0
    cV
    wne
    @2
    wn
    cV
    @0
    necom
    @0
    cV
    cG
    cnx
    cbs
    fvex
    snstrvtxval.v
    snstrvtxval.g
    funsndifnop
    sylbi
    iffalsed
    @6
    @5
    wceq
    @1
    cG
    vtxval
    a1i
    cV
    cvv
    wcel
    cV
    @4
    wceq
    @1
    snstrvtxval.v
    cV
    cG
    cvv
    snstrvtxval.g
    1strbas
    mp1i
    3eqtr4d
end
