include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "wfn.mm"
include "wceq.mm"
include "cn.mm"
include "lencl.mm"
include "cz.mm"
include "clt.mm"
include "nn0z.mm"
include "adantr.mm"
include "0red.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nn0re.mm"
include "2pos.mm"
include "simpr.mm"
include "ltletrd.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "sylan.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "ccnv.mm"
include "cif.mm"
include "fvex.mm"
include "ifex.mm"
include "fnmpti.mm"
include "ffzo0hash.mm"
include "sylancl.mm"

theorem clwlkclwwlklem2a2
  let vx: setvar x
  let cP: class P
  let cE: class E
  let cF: class F
  let cV: class V
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  assert |- ( ( P e. Word V /\ 2 <_ ( # ` P ) ) -> ( # ` F ) = ( ( # ` P ) - 1 ) )

  proof
    cP
    cV
    cword
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @1
    c1
    cmin
    co
    #
    cn0
    wcel
    #
    cF
    cc0
    @4
    cfzo
    co
    #
    wfn
    cF
    chash
    cfv
    @4
    wceq
    @3
    @1
    cn
    wcel
    #
    @5
    @0
    @1
    cn0
    wcel
    #
    @2
    @7
    cV
    cP
    lencl
    @8
    @2
    wa
    #
    @1
    cz
    wcel
    #
    cc0
    @1
    clt
    wbr
    @7
    @8
    @10
    @2
    @1
    nn0z
    adantr
    @9
    cc0
    c2
    @1
    @9
    0red
    c2
    cr
    wcel
    @9
    2re
    a1i
    @8
    @1
    cr
    wcel
    @2
    @1
    nn0re
    adantr
    cc0
    c2
    clt
    wbr
    @9
    2pos
    a1i
    @8
    @2
    simpr
    ltletrd
    @1
    elnnz
    sylanbrc
    sylan
    @1
    nnm1nn0
    syl
    vx
    @6
    vx
    cv
    #
    @1
    c2
    cmin
    co
    clt
    wbr
    #
    @11
    cP
    cfv
    #
    @11
    c1
    caddc
    co
    cP
    cfv
    cpr
    #
    cE
    ccnv
    #
    cfv
    #
    @13
    cc0
    cP
    cfv
    cpr
    #
    @15
    cfv
    #
    cif
    cF
    @12
    @16
    @18
    @14
    @15
    fvex
    @17
    @15
    fvex
    ifex
    clwlkclwwlklem2.f
    fnmpti
    cF
    @4
    ffzo0hash
    sylancl
end
