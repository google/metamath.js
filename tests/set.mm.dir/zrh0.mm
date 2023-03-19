include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "cghm.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "zrhrhm.mm"
include "rhmghm.mm"
include "zring0.mm"
include "ghmid.mm"
include "3syl.mm"

theorem zrh0
  let cR: class R
  let cL: class L
  let c.0: class .0.
  assume zrh0.l: |- L = ( ZRHom ` R )
  assume zrh0.z: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( L ` 0 ) = .0. )

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
    cL
    zring
    cR
    cghm
    co
    wcel
    cc0
    cL
    cfv
    c.0
    wceq
    cR
    cL
    zrh0.l
    zrhrhm
    zring
    cR
    cL
    rhmghm
    zring
    cR
    cL
    cc0
    c.0
    zring0
    zrh0.z
    ghmid
    3syl
end
