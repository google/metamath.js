include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cn.mm"
include "n0i.mm"
include "cdm.mm"
include "cr.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "ovex.mm"
include "df-ee.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "nsyl2.mm"

theorem eleenn
  let cA: class A
  let cN: class N
  let vn: setvar n


  assert |- ( A e. ( EE ` N ) -> N e. NN )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    @0
    c0
    wceq
    #
    cN
    cn
    wcel
    #
    @0
    cA
    n0i
    @2
    cN
    cee
    cdm
    #
    wcel
    @1
    @3
    cn
    cN
    vn
    cn
    cr
    c1
    vn
    cv
    cfz
    co
    #
    cmap
    co
    cee
    cr
    @4
    cmap
    ovex
    vn
    df-ee
    dmmpti
    eleq2i
    cN
    cee
    ndmfv
    sylnbir
    nsyl2
end
