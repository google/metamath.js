include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "zrhrhmb.mm"
include "mpbiri.mm"

theorem zrhrhm
  let cR: class R
  let cL: class L
  let vr: setvar r
  let vs: setvar s
  let cN: class N
  let vn: setvar n
  let c.1: class .1.
  let c.x: class .x.
  assume zrhval.l: |- L = ( ZRHom ` R )


  assert |- ( R e. Ring -> L e. ( ZZring RingHom R ) )

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
    cL
    wceq
    cL
    eqid
    cR
    cL
    cL
    zrhval.l
    zrhrhmb
    mpbiri
end
