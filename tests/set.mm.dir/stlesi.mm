include "cst.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cch.mm"
include "stle1.mm"
include "mpi.mm"
include "adantr.mm"
include "stlei.mm"
include "imp.mm"
include "adantrr.mm"
include "wb.mm"
include "breq1.mm"
include "ad2antll.mm"
include "mpbid.mm"
include "cr.mm"
include "stcl.mm"
include "1re.mm"
include "jctir.mm"
include "letri3.mm"
include "syl.mm"
include "mpbir2and.mm"
include "exp32.mm"

theorem stlesi
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( A C_ B -> ( ( S ` A ) = 1 -> ( S ` B ) = 1 ) ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cB
    wss
    #
    cA
    cS
    cfv
    #
    c1
    wceq
    #
    cB
    cS
    cfv
    #
    c1
    wceq
    #
    @0
    @1
    @3
    wa
    #
    wa
    #
    @5
    @4
    c1
    cle
    wbr
    #
    c1
    @4
    cle
    wbr
    #
    @0
    @8
    @6
    @0
    cB
    cch
    wcel
    #
    @8
    stle.2
    cB
    cS
    stle1
    mpi
    adantr
    @7
    @2
    @4
    cle
    wbr
    #
    @9
    @0
    @1
    @11
    @3
    @0
    @1
    @11
    cA
    cB
    cS
    stle.1
    stle.2
    stlei
    imp
    adantrr
    @3
    @11
    @9
    wb
    @0
    @1
    @2
    c1
    @4
    cle
    breq1
    ad2antll
    mpbid
    @7
    @4
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    #
    @5
    @8
    @9
    wa
    wb
    @0
    @14
    @6
    @0
    @12
    @13
    @0
    @10
    @12
    stle.2
    cB
    cS
    stcl
    mpi
    1re
    jctir
    adantr
    @4
    c1
    letri3
    syl
    mpbir2and
    exp32
end
