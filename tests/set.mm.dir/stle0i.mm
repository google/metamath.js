include "cst.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cch.mm"
include "stge0.mm"
include "mpi.mm"
include "anim2i.mm"
include "expcom.mm"
include "cr.mm"
include "wb.mm"
include "stcl.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "sylibrd.mm"
include "0le0.mm"
include "breq1.mm"
include "mpbiri.mm"
include "impbid1.mm"

theorem stle0i
  let cA: class A
  let cS: class S
  assume sto1.1: |- A e. CH


  assert |- ( S e. States -> ( ( S ` A ) <_ 0 <-> ( S ` A ) = 0 ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cS
    cfv
    #
    cc0
    cle
    wbr
    #
    @1
    cc0
    wceq
    #
    @0
    @2
    @2
    cc0
    @1
    cle
    wbr
    #
    wa
    #
    @3
    @2
    @0
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
    stge0
    mpi
    anim2i
    expcom
    @0
    @1
    cr
    wcel
    #
    cc0
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
    0re
    @1
    cc0
    letri3
    sylancl
    sylibrd
    @3
    @2
    cc0
    cc0
    cle
    wbr
    0le0
    @1
    cc0
    cc0
    cle
    breq1
    mpbiri
    impbid1
end
