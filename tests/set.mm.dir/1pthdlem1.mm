include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "c0.mm"
include "fun0.mm"
include "cs1.mm"
include "fveq2i.mm"
include "s1len.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fzo0.mm"
include "reseq2i.mm"
include "res0.mm"
include "cnveqi.mm"
include "cnv0.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem 1pthdlem1
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">


  assert |- Fun `' ( P |` ( 1 ..^ ( # ` F ) ) )

  proof
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    #
    ccnv
    #
    wfun
    c0
    wfun
    fun0
    @3
    c0
    @3
    c0
    ccnv
    c0
    @2
    c0
    @2
    cP
    c0
    cres
    c0
    @1
    c0
    cP
    @1
    c1
    c1
    cfzo
    co
    c0
    @0
    c1
    c1
    cfzo
    @0
    cJ
    cs1
    #
    chash
    cfv
    c1
    cF
    @4
    chash
    1wlkd.f
    fveq2i
    cJ
    s1len
    eqtri
    oveq2i
    c1
    fzo0
    eqtri
    reseq2i
    cP
    res0
    eqtri
    cnveqi
    cnv0
    eqtri
    funeqi
    mpbir
end
