include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdm.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "funres.mm"
include "adantl.mm"
include "adantr.mm"
include "funsng.mm"
include "dmres.mm"
include "ineq1i.mm"
include "in32.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "0in.mm"
include "3eqtri.mm"
include "a1i.mm"
include "funun.mm"
include "syl21anc.mm"
include "wb.mm"
include "opex.mm"
include "setsvalg.mm"
include "sylan2.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem setsfun
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( ( G e. V /\ Fun G ) /\ ( I e. U /\ E e. W ) ) -> Fun ( G sSet <. I , E >. ) )

  proof
    cG
    cV
    wcel
    #
    cG
    wfun
    #
    wa
    #
    cI
    cU
    wcel
    cE
    cW
    wcel
    wa
    #
    wa
    #
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    wfun
    #
    cG
    cvv
    @5
    csn
    #
    cdm
    #
    cdif
    #
    cres
    #
    @8
    cun
    #
    wfun
    #
    @4
    @11
    wfun
    #
    @8
    wfun
    #
    @11
    cdm
    #
    @9
    cin
    #
    c0
    wceq
    #
    @13
    @2
    @14
    @3
    @1
    @14
    @0
    @10
    cG
    funres
    adantl
    adantr
    @3
    @15
    @2
    cI
    cE
    cU
    cW
    funsng
    adantl
    @18
    @4
    @17
    @10
    cG
    cdm
    #
    cin
    #
    @9
    cin
    #
    c0
    @16
    @20
    @9
    cG
    @10
    dmres
    ineq1i
    @21
    @10
    @9
    cin
    #
    @19
    cin
    c0
    @19
    cin
    c0
    @10
    @19
    @9
    in32
    @22
    c0
    @19
    @22
    @9
    @10
    cin
    c0
    @10
    @9
    incom
    @9
    cvv
    disjdif
    eqtri
    ineq1i
    @19
    0in
    3eqtri
    eqtri
    a1i
    @11
    @8
    funun
    syl21anc
    @2
    @7
    @13
    wb
    @3
    @2
    @6
    @12
    @1
    @0
    @5
    cvv
    wcel
    #
    @6
    @12
    wceq
    @23
    @1
    cI
    cE
    opex
    a1i
    @5
    cG
    cV
    cvv
    setsvalg
    sylan2
    funeqd
    adantr
    mpbird
end
