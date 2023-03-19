include "crg.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "wf1.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "zrhchr.mm"
include "zrhf1ker.mm"
include "bitrd.mm"

theorem zrhker
  let cB: class B
  let cR: class R
  let cL: class L
  let c.0: class .0.
  let vx: setvar x
  assume zrhker.0: |- B = ( Base ` R )
  assume zrhker.1: |- L = ( ZRHom ` R )
  assume zrhker.2: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( ( chr ` R ) = 0 <-> ( `' L " { .0. } ) = { 0 } ) )

  proof
    cR
    crg
    wcel
    cR
    cchr
    cfv
    cc0
    wceq
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
    cB
    cR
    cL
    c.0
    zrhker.0
    zrhker.1
    zrhker.2
    zrhchr
    cB
    cR
    cL
    c.0
    zrhker.0
    zrhker.1
    zrhker.2
    zrhf1ker
    bitrd
end
