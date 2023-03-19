include "cc0.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "cfzo.mm"
include "w3o.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cprime.mm"
include "cn0.mm"
include "wb.mm"
include "4nn0.mm"
include "el1fzopredsuc.mm"
include "ax-mp.mm"
include "fveq2.mm"
include "fmtno0prm.mm"
include "syl6eqel.mm"
include "c2.mm"
include "c3.mm"
include "ctp.mm"
include "eltpi.mm"
include "fmtno1prm.mm"
include "fmtno2prm.mm"
include "fmtno3prm.mm"
include "3jaoi.mm"
include "syl.mm"
include "fzo1to4tp.mm"
include "eleq2s.mm"
include "fmtno4prm.mm"
include "sylbi.mm"

theorem fmtnofz04prm
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. ( 0 ... 4 ) -> ( FermatNo ` N ) e. Prime )

  proof
    cN
    cc0
    c4
    cfz
    co
    wcel
    #
    cN
    cc0
    wceq
    #
    cN
    c1
    c4
    cfzo
    co
    #
    wcel
    #
    cN
    c4
    wceq
    #
    w3o
    #
    cN
    cfmtno
    cfv
    #
    cprime
    wcel
    #
    c4
    cn0
    wcel
    @0
    @5
    wb
    4nn0
    cN
    c4
    el1fzopredsuc
    ax-mp
    @1
    @7
    @3
    @4
    @1
    @6
    cc0
    cfmtno
    cfv
    cprime
    cN
    cc0
    cfmtno
    fveq2
    fmtno0prm
    syl6eqel
    @7
    cN
    c1
    c2
    c3
    ctp
    #
    @2
    cN
    @8
    wcel
    cN
    c1
    wceq
    #
    cN
    c2
    wceq
    #
    cN
    c3
    wceq
    #
    w3o
    @7
    cN
    c1
    c2
    c3
    eltpi
    @9
    @7
    @10
    @11
    @9
    @6
    c1
    cfmtno
    cfv
    cprime
    cN
    c1
    cfmtno
    fveq2
    fmtno1prm
    syl6eqel
    @10
    @6
    c2
    cfmtno
    cfv
    cprime
    cN
    c2
    cfmtno
    fveq2
    fmtno2prm
    syl6eqel
    @11
    @6
    c3
    cfmtno
    cfv
    cprime
    cN
    c3
    cfmtno
    fveq2
    fmtno3prm
    syl6eqel
    3jaoi
    syl
    fzo1to4tp
    eleq2s
    @4
    @6
    c4
    cfmtno
    cfv
    cprime
    cN
    c4
    cfmtno
    fveq2
    fmtno4prm
    syl6eqel
    3jaoi
    sylbi
end
