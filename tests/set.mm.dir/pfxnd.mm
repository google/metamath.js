include "cword.mm"
include "wcel.mm"
include "cn0.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cpfx.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "c0.mm"
include "wceq.mm"
include "pfxval.mm"
include "3adant3.mm"
include "cz.mm"
include "cle.mm"
include "w3o.mm"
include "simp1.mm"
include "0zd.mm"
include "nn0z.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "3mix3.mm"
include "3ad2ant3.mm"
include "swrdnd.mm"
include "sylc.mm"
include "eqtrd.mm"

theorem pfxnd
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( W e. Word V /\ L e. NN0 /\ ( # ` W ) < L ) -> ( W prefix L ) = (/) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cL
    cn0
    wcel
    #
    cW
    chash
    cfv
    cL
    clt
    wbr
    #
    w3a
    #
    cW
    cL
    cpfx
    co
    #
    cW
    cc0
    cL
    cop
    csubstr
    co
    #
    c0
    @1
    @2
    @5
    @6
    wceq
    @3
    cW
    cL
    @0
    pfxval
    3adant3
    @4
    @1
    cc0
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    w3a
    cc0
    cc0
    clt
    wbr
    #
    cL
    cc0
    cle
    wbr
    #
    @3
    w3o
    #
    @6
    c0
    wceq
    @4
    @1
    @7
    @8
    @1
    @2
    @3
    simp1
    @4
    0zd
    @2
    @1
    @8
    @3
    cL
    nn0z
    3ad2ant2
    3jca
    @3
    @1
    @11
    @2
    @3
    @9
    @10
    3mix3
    3ad2ant3
    cc0
    cL
    cV
    cW
    swrdnd
    sylc
    eqtrd
end
