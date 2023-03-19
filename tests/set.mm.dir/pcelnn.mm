include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "cdvds.mm"
include "cz.mm"
include "wb.mm"
include "nnz.mm"
include "cn0.mm"
include "1nn0.mm"
include "pcdvdsb.mm"
include "mp3an3.mm"
include "sylan2.mm"
include "pccl.mm"
include "elnnnn0c.mm"
include "baibr.mm"
include "syl.mm"
include "wceq.mm"
include "prmnn.mm"
include "nncnd.mm"
include "exp1d.mm"
include "adantr.mm"
include "breq1d.mm"
include "3bitr3d.mm"

theorem pcelnn
  let cP: class P
  let cN: class N


  assert |- ( ( P e. Prime /\ N e. NN ) -> ( ( P pCnt N ) e. NN <-> P || N ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    c1
    cP
    cN
    cpc
    co
    #
    cle
    wbr
    #
    cP
    c1
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @3
    cn
    wcel
    #
    cP
    cN
    cdvds
    wbr
    @1
    @0
    cN
    cz
    wcel
    #
    @4
    @6
    wb
    #
    cN
    nnz
    @0
    @8
    c1
    cn0
    wcel
    @9
    1nn0
    c1
    cP
    cN
    pcdvdsb
    mp3an3
    sylan2
    @2
    @3
    cn0
    wcel
    #
    @4
    @7
    wb
    cP
    cN
    pccl
    @7
    @10
    @4
    @3
    elnnnn0c
    baibr
    syl
    @2
    @5
    cP
    cN
    cdvds
    @0
    @5
    cP
    wceq
    @1
    @0
    cP
    @0
    cP
    cP
    prmnn
    nncnd
    exp1d
    adantr
    breq1d
    3bitr3d
end
