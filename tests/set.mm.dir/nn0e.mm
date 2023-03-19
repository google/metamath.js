include "cn0.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "nn0re.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "evendiv2z.mm"
include "anim12ci.mm"
include "elnn0z.mm"
include "sylibr.mm"

theorem nn0e
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ N e. Even ) -> ( N / 2 ) e. NN0 )

  proof
    cN
    cn0
    wcel
    #
    cN
    ceven
    wcel
    #
    wa
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @2
    cn0
    wcel
    @0
    @4
    @1
    @3
    @0
    cc0
    cN
    cle
    wbr
    #
    @4
    cN
    nn0ge0
    @0
    cN
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @5
    @4
    wb
    cN
    nn0re
    @6
    @0
    2re
    a1i
    @7
    @0
    2pos
    a1i
    cN
    c2
    ge0div
    syl3anc
    mpbid
    cN
    evendiv2z
    anim12ci
    @2
    elnn0z
    sylibr
end
