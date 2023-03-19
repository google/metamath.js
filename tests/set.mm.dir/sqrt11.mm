include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "resqrtcl.mm"
include "sqrtge0.mm"
include "jca.mm"
include "sq11.mm"
include "syl2an.mm"
include "resqrtth.mm"
include "eqeqan12d.mm"
include "bitr3d.mm"

theorem sqrt11
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( sqrt ` A ) = ( sqrt ` B ) <-> A = B ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    wa
    #
    wa
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    cB
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    #
    @2
    @4
    wceq
    #
    cA
    cB
    wceq
    @0
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    wa
    @6
    @7
    wb
    @1
    @0
    @8
    @9
    cA
    resqrtcl
    cA
    sqrtge0
    jca
    @1
    @10
    @11
    cB
    resqrtcl
    cB
    sqrtge0
    jca
    @2
    @4
    sq11
    syl2an
    @0
    @1
    @3
    cA
    @5
    cB
    cA
    resqrtth
    cB
    resqrtth
    eqeqan12d
    bitr3d
end
