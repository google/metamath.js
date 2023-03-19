include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "df-suc.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wceq.mm"
include "com.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "word.mm"
include "nnord.mm"
include "ordirr.mm"
include "mp2b.mm"
include "wa.mm"
include "wi.mm"
include "hashunsng.mm"
include "mp2an.mm"
include "oveq1i.mm"

theorem hashp1i
  let cA: class A
  let cB: class B
  let cM: class M
  let cN: class N
  assume hashp1i.1: |- A e. _om
  assume hashp1i.2: |- B = suc A
  assume hashp1i.3: |- ( # ` A ) = M
  assume hashp1i.4: |- ( M + 1 ) = N


  assert |- ( # ` B ) = N

  proof
    cB
    chash
    cfv
    cA
    cA
    csn
    cun
    #
    chash
    cfv
    #
    cN
    cB
    @0
    chash
    cB
    cA
    csuc
    @0
    hashp1i.2
    cA
    df-suc
    eqtri
    fveq2i
    @1
    cA
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cN
    cA
    cfn
    wcel
    #
    cA
    cA
    wcel
    wn
    #
    @1
    @3
    wceq
    #
    cA
    com
    wcel
    #
    @4
    hashp1i.1
    cA
    nnfi
    ax-mp
    @7
    cA
    word
    @5
    hashp1i.1
    cA
    nnord
    cA
    ordirr
    mp2b
    @7
    @4
    @5
    wa
    @6
    wi
    hashp1i.1
    cA
    cA
    com
    hashunsng
    ax-mp
    mp2an
    @3
    cM
    c1
    caddc
    co
    cN
    @2
    cM
    c1
    caddc
    hashp1i.3
    oveq1i
    hashp1i.4
    eqtri
    eqtri
    eqtri
end
