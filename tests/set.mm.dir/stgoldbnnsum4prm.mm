include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbo.mm"
include "wcel.mm"
include "wi.mm"
include "codd.mm"
include "wral.mm"
include "c5.mm"
include "cgbow.mm"
include "c4.mm"
include "cle.mm"
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
include "c2.mm"
include "cuz.mm"
include "stgoldbwt.mm"
include "wtgoldbnnsum4prm.mm"
include "syl.mm"

theorem stgoldbnnsum4prm
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vd: setvar d
  let cN: class N
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vo: setvar o
  let vg: setvar g
  let vx: setvar x

  disjoint f k
  disjoint f m
  disjoint k m
  disjoint d f
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint f n
  disjoint k n
  disjoint m n
  disjoint N f
  disjoint N k
  disjoint N m
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint N o
  disjoint N g
  disjoint f g
  disjoint f o
  disjoint g k
  disjoint g m
  disjoint g o
  disjoint k o
  disjoint m o
  disjoint k x
  assert |- ( A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) -> A. n e. ( ZZ>= ` 2 ) E. d e. NN E. f e. ( Prime ^m ( 1 ... d ) ) ( d <_ 4 /\ n = sum_ k e. ( 1 ... d ) ( f ` k ) ) )

  proof
    c7
    vm
    cv
    #
    clt
    wbr
    @0
    cgbo
    wcel
    wi
    vm
    codd
    wral
    c5
    @0
    clt
    wbr
    @0
    cgbow
    wcel
    wi
    vm
    codd
    wral
    vd
    cv
    #
    c4
    cle
    wbr
    vn
    cv
    c1
    @1
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
    wa
    vf
    cprime
    @2
    cmap
    co
    wrex
    vd
    cn
    wrex
    vn
    c2
    cuz
    cfv
    wral
    vm
    stgoldbwt
    vf
    vk
    vm
    vn
    vd
    wtgoldbnnsum4prm
    syl
end
