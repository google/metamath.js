include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "simpr.mm"
include "nn0cnd.mm"
include "mulid2d.mm"
include "1red.mm"
include "cr.mm"
include "nnre.mm"
include "adantr.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "wbr.mm"
include "nnge1.mm"
include "lemul1ad.mm"
include "eqbrtrrd.mm"

theorem nnmulge
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN0 ) -> N <_ ( M x. N ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    c1
    cN
    cmul
    co
    cN
    cM
    cN
    cmul
    co
    cle
    @2
    cN
    @2
    cN
    @0
    @1
    simpr
    #
    nn0cnd
    mulid2d
    @2
    c1
    cM
    cN
    @2
    1red
    @0
    cM
    cr
    wcel
    @1
    cM
    nnre
    adantr
    @2
    cN
    @3
    nn0red
    @2
    cN
    @3
    nn0ge0d
    @0
    c1
    cM
    cle
    wbr
    @1
    cM
    nnge1
    adantr
    lemul1ad
    eqbrtrrd
end
