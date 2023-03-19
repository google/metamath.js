include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "cz.mm"
include "wf1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "zring0.mm"
include "kerf1hrm.mm"
include "syl.mm"

theorem zrhf1ker
  let cB: class B
  let cR: class R
  let cL: class L
  let c.0: class .0.
  assume zrhker.0: |- B = ( Base ` R )
  assume zrhker.1: |- L = ( ZRHom ` R )
  assume zrhker.2: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( L : ZZ -1-1-> B <-> ( `' L " { .0. } ) = { 0 } ) )

  proof
    cR
    crg
    wcel
    cL
    zring
    cR
    crh
    co
    wcel
    cz
    cB
    cL
    wf1
    cL
    ccnv
    c.0
    csn
    cima
    cc0
    csn
    wceq
    wb
    cR
    cL
    zrhker.1
    zrhrhm
    cz
    cB
    zring
    cR
    cL
    cc0
    c.0
    zringbas
    zrhker.0
    zring0
    zrhker.2
    kerf1hrm
    syl
end
