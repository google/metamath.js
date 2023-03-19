include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cop.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cif.mm"
include "cioo.mm"
include "crn.mm"
include "eqeq1.mm"
include "infeq1.mm"
include "supeq1.mm"
include "opeq12d.mm"
include "ifbieq2d.mm"
include "opex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem ioorval
  let vx: setvar x
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  assume ioorf.1: |- F = ( x e. ran (,) |-> if ( x = (/) , <. 0 , 0 >. , <. inf ( x , RR* , < ) , sup ( x , RR* , < ) >. ) )

  disjoint A x
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F a
  disjoint F b
  assert |- ( A e. ran (,) -> ( F ` A ) = if ( A = (/) , <. 0 , 0 >. , <. inf ( A , RR* , < ) , sup ( A , RR* , < ) >. ) )

  proof
    vx
    cA
    vx
    cv
    #
    c0
    wceq
    #
    cc0
    cc0
    cop
    #
    @0
    cxr
    clt
    cinf
    #
    @0
    cxr
    clt
    csup
    #
    cop
    #
    cif
    cA
    c0
    wceq
    #
    @2
    cA
    cxr
    clt
    cinf
    #
    cA
    cxr
    clt
    csup
    #
    cop
    #
    cif
    cioo
    crn
    cF
    @0
    cA
    wceq
    #
    @1
    @6
    @5
    @9
    @2
    @0
    cA
    c0
    eqeq1
    @10
    @3
    @7
    @4
    @8
    cxr
    @0
    cA
    clt
    infeq1
    cxr
    @0
    cA
    clt
    supeq1
    opeq12d
    ifbieq2d
    ioorf.1
    @6
    @2
    @9
    cc0
    cc0
    opex
    @7
    @8
    opex
    ifex
    fvmpt
end
