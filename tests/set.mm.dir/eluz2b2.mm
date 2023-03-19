include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "eluz2b1.mm"
include "cle.mm"
include "cr.mm"
include "wi.mm"
include "1re.mm"
include "zre.mm"
include "ltle.mm"
include "sylancr.mm"
include "imdistani.mm"
include "elnnz1.mm"
include "sylibr.mm"
include "simpr.mm"
include "jca.mm"
include "nnz.mm"
include "anim1i.mm"
include "impbii.mm"
include "bitri.mm"

theorem eluz2b2
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) <-> ( N e. NN /\ 1 < N ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    #
    cN
    cn
    wcel
    #
    @1
    wa
    #
    cN
    eluz2b1
    @2
    @4
    @2
    @3
    @1
    @2
    @0
    c1
    cN
    cle
    wbr
    #
    wa
    @3
    @0
    @1
    @5
    @0
    c1
    cr
    wcel
    cN
    cr
    wcel
    @1
    @5
    wi
    1re
    cN
    zre
    c1
    cN
    ltle
    sylancr
    imdistani
    cN
    elnnz1
    sylibr
    @0
    @1
    simpr
    jca
    @3
    @0
    @1
    cN
    nnz
    anim1i
    impbii
    bitri
end
