include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "wceq.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "wf.mm"
include "eleei.mm"
include "cdm.mm"
include "fdm.mm"
include "sylan9req.mm"
include "syl2an.mm"
include "cuz.mm"
include "wb.mm"
include "cn.mm"
include "eleenn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "fzopth.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"

theorem eedimeq
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ( EE ` N ) /\ A e. ( EE ` M ) ) -> N = M )

  proof
    cA
    cN
    cee
    cfv
    wcel
    #
    cA
    cM
    cee
    cfv
    wcel
    #
    wa
    #
    c1
    c1
    wceq
    #
    cN
    cM
    wceq
    #
    @2
    c1
    cN
    cfz
    co
    #
    c1
    cM
    cfz
    co
    #
    wceq
    #
    @3
    @4
    wa
    #
    @0
    @5
    cr
    cA
    wf
    #
    @6
    cr
    cA
    wf
    #
    @7
    @1
    cA
    cN
    eleei
    cA
    cM
    eleei
    @9
    @10
    @5
    cA
    cdm
    @6
    @5
    cr
    cA
    fdm
    @6
    cr
    cA
    fdm
    sylan9req
    syl2an
    @2
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @7
    @8
    wb
    @0
    @12
    @1
    @0
    cN
    cn
    @11
    cA
    cN
    eleenn
    nnuz
    syl6eleq
    adantr
    c1
    cM
    c1
    cN
    fzopth
    syl
    mpbid
    simprd
end
