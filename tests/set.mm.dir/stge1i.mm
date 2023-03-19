include "cst.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cch.mm"
include "stle1.mm"
include "mpi.mm"
include "anim1i.mm"
include "ex.mm"
include "cr.mm"
include "wb.mm"
include "stcl.mm"
include "1re.mm"
include "letri3.mm"
include "sylancl.mm"
include "sylibrd.mm"
include "1le1.mm"
include "breq2.mm"
include "mpbiri.mm"
include "impbid1.mm"

theorem stge1i
  let cA: class A
  let cS: class S
  assume sto1.1: |- A e. CH


  assert |- ( S e. States -> ( 1 <_ ( S ` A ) <-> ( S ` A ) = 1 ) )

  proof
    cS
    cst
    wcel
    #
    c1
    cA
    cS
    cfv
    #
    cle
    wbr
    #
    @1
    c1
    wceq
    #
    @0
    @2
    @1
    c1
    cle
    wbr
    #
    @2
    wa
    #
    @3
    @0
    @2
    @5
    @0
    @4
    @2
    @0
    cA
    cch
    wcel
    #
    @4
    sto1.1
    cA
    cS
    stle1
    mpi
    anim1i
    ex
    @0
    @1
    cr
    wcel
    #
    c1
    cr
    wcel
    @3
    @5
    wb
    @0
    @6
    @7
    sto1.1
    cA
    cS
    stcl
    mpi
    1re
    @1
    c1
    letri3
    sylancl
    sylibrd
    @3
    @2
    c1
    c1
    cle
    wbr
    1le1
    @1
    c1
    c1
    cle
    breq2
    mpbiri
    impbid1
end
