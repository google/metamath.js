include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "casin.mm"
include "cfv.mm"
include "csin.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cres.mm"
include "ccnv.mm"
include "wceq.mm"
include "wf1o.mm"
include "wf.mm"
include "resinf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "ffvelrni.mm"
include "fvres.mm"
include "syl.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "reasinsin.mm"
include "eqeltrd.mm"

theorem asinrebnd
  let cA: class A


  assert |- ( A e. ( -u 1 [,] 1 ) -> ( arcsin ` A ) e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) )

  proof
    cA
    c1
    cneg
    c1
    cicc
    co
    #
    wcel
    #
    cA
    casin
    cfv
    #
    cA
    csin
    cpi
    c2
    cdiv
    co
    #
    cneg
    @3
    cicc
    co
    #
    cres
    #
    ccnv
    #
    cfv
    #
    @4
    @1
    @7
    csin
    cfv
    #
    casin
    cfv
    #
    @2
    @7
    @1
    @8
    cA
    casin
    @1
    @7
    @5
    cfv
    #
    @8
    cA
    @1
    @7
    @4
    wcel
    #
    @10
    @8
    wceq
    @0
    @4
    cA
    @6
    @4
    @0
    @5
    wf1o
    #
    @0
    @4
    @6
    wf1o
    @0
    @4
    @6
    wf
    resinf1o
    @4
    @0
    @5
    f1ocnv
    @0
    @4
    @6
    f1of
    mp2b
    ffvelrni
    #
    @7
    @4
    csin
    fvres
    syl
    @12
    @1
    @10
    cA
    wceq
    resinf1o
    @4
    @0
    cA
    @5
    f1ocnvfv2
    mpan
    eqtr3d
    fveq2d
    @1
    @11
    @9
    @7
    wceq
    @13
    @7
    reasinsin
    syl
    eqtr3d
    @13
    eqeltrd
end
