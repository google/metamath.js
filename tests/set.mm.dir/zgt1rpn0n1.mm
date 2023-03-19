include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "eluz2nn.mm"
include "nnrpd.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "2pos.mm"
include "0re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "eluzle.mm"
include "mto.mm"
include "nelne2.mm"
include "mpan2.mm"
include "1nuz2.mm"
include "3jca.mm"

theorem zgt1rpn0n1
  let cB: class B


  assert |- ( B e. ( ZZ>= ` 2 ) -> ( B e. RR+ /\ B =/= 0 /\ B =/= 1 ) )

  proof
    cB
    c2
    cuz
    cfv
    #
    wcel
    #
    cB
    crp
    wcel
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    @1
    cB
    cB
    eluz2nn
    nnrpd
    @1
    cc0
    @0
    wcel
    #
    wn
    @2
    @4
    c2
    cc0
    cle
    wbr
    #
    cc0
    c2
    clt
    wbr
    @5
    wn
    2pos
    cc0
    c2
    0re
    2re
    ltnlei
    mpbi
    c2
    cc0
    eluzle
    mto
    cB
    cc0
    @0
    nelne2
    mpan2
    @1
    c1
    @0
    wcel
    wn
    @3
    1nuz2
    cB
    c1
    @0
    nelne2
    mpan2
    3jca
end
