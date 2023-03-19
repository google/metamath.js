include "wcel.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cfv.mm"
include "cz.mm"
include "0z.mm"
include "a1i.mm"
include "id.mm"
include "fsnd.mm"
include "fvsng.mm"
include "mpan.mm"
include "jca.mm"
include "adantr.mm"
include "wb.mm"
include "fz0sn.mm"
include "feq12d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "mpbird.mm"

theorem 1fv
  let cP: class P
  let cN: class N
  let cV: class V


  assert |- ( ( N e. V /\ P = { <. 0 , N >. } ) -> ( P : ( 0 ... 0 ) --> V /\ ( P ` 0 ) = N ) )

  proof
    cN
    cV
    wcel
    #
    cP
    cc0
    cN
    cop
    csn
    #
    wceq
    #
    wa
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    cc0
    cP
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cc0
    csn
    #
    cV
    @1
    wf
    #
    cc0
    @1
    cfv
    #
    cN
    wceq
    #
    wa
    #
    @0
    @12
    @2
    @0
    @9
    @11
    @0
    cc0
    cN
    cz
    cV
    cc0
    cz
    wcel
    #
    @0
    0z
    a1i
    @0
    id
    fsnd
    @13
    @0
    @11
    0z
    cc0
    cN
    cz
    cV
    fvsng
    mpan
    jca
    adantr
    @2
    @7
    @12
    wb
    @0
    @2
    @4
    @9
    @6
    @11
    @2
    @3
    @8
    cV
    cP
    @1
    @2
    id
    @3
    @8
    wceq
    @2
    fz0sn
    a1i
    feq12d
    @2
    @5
    @10
    cN
    cc0
    cP
    @1
    fveq1
    eqeq1d
    anbi12d
    adantl
    mpbird
end
