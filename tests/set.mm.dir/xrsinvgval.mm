include "cxr.mm"
include "wcel.mm"
include "cxrs.mm"
include "cminusg.mm"
include "cfv.mm"
include "cv.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "crio.mm"
include "cxne.mm"
include "xrsbas.mm"
include "xrsadd.mm"
include "xrs0.mm"
include "eqid.mm"
include "grpinvval.mm"
include "xnegcl.mm"
include "wb.mm"
include "xaddeq0.mm"
include "ancoms.mm"
include "riota5.mm"
include "eqtrd.mm"

theorem xrsinvgval
  let cB: class B
  let vx: setvar x


  assert |- ( B e. RR* -> ( ( invg ` RR*s ) ` B ) = -e B )

  proof
    cB
    cxr
    wcel
    #
    cB
    cxrs
    cminusg
    cfv
    #
    cfv
    vx
    cv
    #
    cB
    cxad
    co
    cc0
    wceq
    #
    vx
    cxr
    crio
    cB
    cxne
    #
    vx
    cxr
    cxad
    cxrs
    @1
    cB
    cc0
    xrsbas
    xrsadd
    xrs0
    @1
    eqid
    grpinvval
    @0
    @3
    vx
    cxr
    @4
    cB
    xnegcl
    @2
    cxr
    wcel
    @0
    @3
    @2
    @4
    wceq
    wb
    @2
    cB
    xaddeq0
    ancoms
    riota5
    eqtrd
end
