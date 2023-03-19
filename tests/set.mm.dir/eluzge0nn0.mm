include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cn0.mm"
include "wi.mm"
include "eluz2.mm"
include "wa.mm"
include "simpl2.mm"
include "cr.mm"
include "zre.mm"
include "0red.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "syl2an.mm"
include "letr.mm"
include "syl.mm"
include "expcomd.mm"
include "ex.mm"
include "3imp1.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "sylbi.mm"

theorem eluzge0nn0
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> ( 0 <_ M -> N e. NN0 ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    cc0
    cM
    cle
    wbr
    #
    cN
    cn0
    wcel
    #
    wi
    cM
    cN
    eluz2
    @3
    @4
    @5
    @3
    @4
    wa
    @1
    cc0
    cN
    cle
    wbr
    #
    @5
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    @6
    @0
    @1
    @2
    @4
    @6
    wi
    wi
    @0
    @1
    wa
    #
    @4
    @2
    @6
    @7
    cc0
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    @4
    @2
    wa
    @6
    wi
    @0
    @9
    @10
    @11
    @1
    cM
    zre
    cN
    zre
    @9
    @10
    wa
    #
    @8
    @9
    @10
    @12
    0red
    @9
    @10
    simpl
    @9
    @10
    simpr
    3jca
    syl2an
    cc0
    cM
    cN
    letr
    syl
    expcomd
    ex
    3imp1
    cN
    elnn0z
    sylanbrc
    ex
    sylbi
end
