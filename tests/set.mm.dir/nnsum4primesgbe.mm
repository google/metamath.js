include "cgbe.mm"
include "wcel.mm"
include "cv.mm"
include "c3.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "c4.mm"
include "nnsum3primesgbe.mm"
include "clt.mm"
include "3lt4.mm"
include "cr.mm"
include "wi.mm"
include "nnre.mm"
include "3re.mm"
include "a1i.mm"
include "4re.mm"
include "leltletr.mm"
include "syl3anc.mm"
include "mpan2i.mm"
include "anim1d.mm"
include "reximdv.mm"
include "reximia.mm"
include "syl.mm"

theorem nnsum4primesgbe
  let vf: setvar f
  let vk: setvar k
  let cN: class N
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x

  disjoint N d
  disjoint N f
  disjoint N k
  disjoint d f
  disjoint d k
  disjoint f k
  disjoint N p
  disjoint N q
  disjoint d p
  disjoint d q
  disjoint f p
  disjoint f q
  disjoint k p
  disjoint k q
  disjoint p q
  disjoint k x
  assert |- ( N e. GoldbachEven -> E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 4 /\ N = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    cN
    cgbe
    wcel
    vd
    cv
    #
    c3
    cle
    wbr
    #
    cN
    c1
    @0
    cfz
    co
    #
    vk
    cv
    vf
    cv
    cfv
    vk
    csu
    wceq
    #
    wa
    #
    vf
    cprime
    @2
    cmap
    co
    #
    wrex
    #
    vd
    cn
    wrex
    @0
    c4
    cle
    wbr
    #
    @3
    wa
    #
    vf
    @5
    wrex
    #
    vd
    cn
    wrex
    vf
    vk
    cN
    vd
    nnsum3primesgbe
    @6
    @9
    vd
    cn
    @0
    cn
    wcel
    #
    @4
    @8
    vf
    @5
    @10
    @1
    @7
    @3
    @10
    @1
    c3
    c4
    clt
    wbr
    #
    @7
    3lt4
    @10
    @0
    cr
    wcel
    c3
    cr
    wcel
    #
    c4
    cr
    wcel
    #
    @1
    @11
    wa
    @7
    wi
    @0
    nnre
    @12
    @10
    3re
    a1i
    @13
    @10
    4re
    a1i
    @0
    c3
    c4
    leltletr
    syl3anc
    mpan2i
    anim1d
    reximdv
    reximia
    syl
end
