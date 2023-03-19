include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "nnz.mm"
include "nnge1.mm"
include "jca.mm"
include "cc0.mm"
include "clt.mm"
include "0lt1.mm"
include "cr.mm"
include "wi.mm"
include "zre.mm"
include "0re.mm"
include "1re.mm"
include "ltletr.mm"
include "mp3an12.mm"
include "syl.mm"
include "mpani.mm"
include "imdistani.mm"
include "elnnz.mm"
include "sylibr.mm"
include "impbii.mm"

theorem elnnz1
  let cN: class N


  assert |- ( N e. NN <-> ( N e. ZZ /\ 1 <_ N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cz
    wcel
    #
    c1
    cN
    cle
    wbr
    #
    wa
    #
    @0
    @1
    @2
    cN
    nnz
    cN
    nnge1
    jca
    @3
    @1
    cc0
    cN
    clt
    wbr
    #
    wa
    @0
    @1
    @2
    @4
    @1
    cc0
    c1
    clt
    wbr
    #
    @2
    @4
    0lt1
    @1
    cN
    cr
    wcel
    #
    @5
    @2
    wa
    @4
    wi
    #
    cN
    zre
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @6
    @7
    0re
    1re
    cc0
    c1
    cN
    ltletr
    mp3an12
    syl
    mpani
    imdistani
    cN
    elnnz
    sylibr
    impbii
end
