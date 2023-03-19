include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cmul.mm"
include "cif.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "eqeq1.mm"
include "id.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "1ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem fourierdlem29
  let cA: class A
  let cK: class K
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem29.1: |- K = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 1 , ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) )

  disjoint A s
  disjoint k x
  assert |- ( A e. ( -u _pi [,] _pi ) -> ( K ` A ) = if ( A = 0 , 1 , ( A / ( 2 x. ( sin ` ( A / 2 ) ) ) ) ) )

  proof
    vs
    cA
    vs
    cv
    #
    cc0
    wceq
    #
    c1
    @0
    c2
    @0
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    cA
    cc0
    wceq
    #
    c1
    cA
    c2
    cA
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    cpi
    cneg
    cpi
    cicc
    co
    cK
    @0
    cA
    wceq
    #
    @1
    @6
    @5
    @10
    c1
    @0
    cA
    cc0
    eqeq1
    @11
    @0
    cA
    @4
    @9
    cdiv
    @11
    id
    @11
    @3
    @8
    c2
    cmul
    @11
    @2
    @7
    csin
    @0
    cA
    c2
    cdiv
    oveq1
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    fourierdlem29.1
    @6
    c1
    @10
    1ex
    cA
    @9
    cdiv
    ovex
    ifex
    fvmpt
end
