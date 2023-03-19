include "cz.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "zre.mm"
include "flle.mm"
include "syl.mm"
include "leidd.mm"
include "wb.mm"
include "flge.mm"
include "mpancom.mm"
include "mpbid.mm"
include "reflcl.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem flid
  let cA: class A


  assert |- ( A e. ZZ -> ( |_ ` A ) = A )

  proof
    cA
    cz
    wcel
    #
    cA
    cfl
    cfv
    #
    cA
    wceq
    @1
    cA
    cle
    wbr
    #
    cA
    @1
    cle
    wbr
    #
    @0
    cA
    cr
    wcel
    #
    @2
    cA
    zre
    #
    cA
    flle
    syl
    @0
    cA
    cA
    cle
    wbr
    #
    @3
    @0
    cA
    @5
    leidd
    @4
    @0
    @6
    @3
    wb
    @5
    cA
    cA
    flge
    mpancom
    mpbid
    @0
    @1
    cA
    @0
    @4
    @1
    cr
    wcel
    @5
    cA
    reflcl
    syl
    @5
    letri3d
    mpbir2and
end
