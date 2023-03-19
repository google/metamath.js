include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cfz.mm"
include "c0.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "fzn.mm"
include "sylancr.mm"
include "cn.mm"
include "wo.mm"
include "elnn0.mm"
include "cle.mm"
include "wn.mm"
include "nnge1.mm"
include "cr.mm"
include "nnre.mm"
include "1re.mm"
include "wa.mm"
include "subge0.mm"
include "0re.mm"
include "resubcl.mm"
include "lenlt.mm"
include "bitr3d.mm"
include "sylancl.mm"
include "mpbid.mm"
include "nnne0.mm"
include "neneqd.mm"
include "2falsed.mm"
include "cneg.mm"
include "oveq1.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "neg1lt0.mm"
include "syl6eqbr.mm"
include "id.mm"
include "2thd.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem fz0n
  let cN: class N


  assert |- ( N e. NN0 -> ( ( 0 ... ( N - 1 ) ) = (/) <-> N = 0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cc0
    clt
    wbr
    #
    cc0
    @1
    cfz
    co
    c0
    wceq
    #
    cN
    cc0
    wceq
    #
    @0
    cc0
    cz
    wcel
    @1
    cz
    wcel
    #
    @2
    @3
    wb
    0z
    @0
    cN
    cz
    wcel
    @5
    cN
    nn0z
    cN
    peano2zm
    syl
    cc0
    @1
    fzn
    sylancr
    @0
    cN
    cn
    wcel
    #
    @4
    wo
    @2
    @4
    wb
    #
    cN
    elnn0
    @6
    @7
    @4
    @6
    @2
    @4
    @6
    c1
    cN
    cle
    wbr
    #
    @2
    wn
    #
    cN
    nnge1
    @6
    cN
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @8
    @9
    wb
    cN
    nnre
    1re
    @10
    @11
    wa
    #
    cc0
    @1
    cle
    wbr
    #
    @8
    @9
    cN
    c1
    subge0
    @12
    cc0
    cr
    wcel
    @1
    cr
    wcel
    @13
    @9
    wb
    0re
    cN
    c1
    resubcl
    cc0
    @1
    lenlt
    sylancr
    bitr3d
    sylancl
    mpbid
    @6
    cN
    cc0
    cN
    nnne0
    neneqd
    2falsed
    @4
    @2
    @4
    @4
    @1
    c1
    cneg
    #
    cc0
    clt
    @4
    @1
    cc0
    c1
    cmin
    co
    @14
    cN
    cc0
    c1
    cmin
    oveq1
    c1
    df-neg
    syl6eqr
    neg1lt0
    syl6eqbr
    @4
    id
    2thd
    jaoi
    sylbi
    bitr3d
end
