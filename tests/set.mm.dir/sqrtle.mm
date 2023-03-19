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
include "wb.mm"
include "resqrtcl.mm"
include "sqrtge0.mm"
include "jca.mm"
include "le2sq.mm"
include "syl2an.mm"
include "resqrtth.mm"
include "breqan12d.mm"
include "bitr2d.mm"

theorem sqrtle
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( A <_ B <-> ( sqrt ` A ) <_ ( sqrt ` B ) ) )

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
    cB
    csqrt
    cfv
    #
    cle
    wbr
    #
    @2
    c2
    cexp
    co
    #
    @3
    c2
    cexp
    co
    #
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
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
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    @4
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
    @3
    le2sq
    syl2an
    @0
    @1
    @5
    cA
    @6
    cB
    cle
    cA
    resqrtth
    cB
    resqrtth
    breqan12d
    bitr2d
end
