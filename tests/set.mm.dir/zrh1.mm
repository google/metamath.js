include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "c1.mm"
include "cfv.mm"
include "wceq.mm"
include "zrhrhm.mm"
include "zring1.mm"
include "rhm1.mm"
include "syl.mm"

theorem zrh1
  let cR: class R
  let c.1: class .1.
  let cL: class L
  assume zrh1.l: |- L = ( ZRHom ` R )
  assume zrh1.o: |- .1. = ( 1r ` R )


  assert |- ( R e. Ring -> ( L ` 1 ) = .1. )

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
    c1
    cL
    cfv
    c.1
    wceq
    cR
    cL
    zrh1.l
    zrhrhm
    zring
    cR
    c1
    cL
    c.1
    zring1
    zrh1.o
    rhm1
    syl
end
