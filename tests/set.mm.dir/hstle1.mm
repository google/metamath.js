include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cfv.mm"
include "cno.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cort.mm"
include "caddc.mm"
include "cc0.mm"
include "chil.mm"
include "cr.mm"
include "choccl.mm"
include "hstcl.mm"
include "sylan2.mm"
include "normcl.mm"
include "syl.mm"
include "sqge0d.mm"
include "resqcld.mm"
include "addge01d.mm"
include "mpbid.mm"
include "hstnmoc.mm"
include "sq1.mm"
include "syl6eqr.mm"
include "breqtrd.mm"
include "wb.mm"
include "normge0.mm"
include "1re.mm"
include "0le1.mm"
include "le2sq.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem hstle1
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( normh ` ( S ` A ) ) <_ 1 )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    #
    cA
    cS
    cfv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @4
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @2
    @6
    @6
    cA
    cort
    cfv
    #
    cS
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @7
    cle
    @2
    cc0
    @12
    cle
    wbr
    @6
    @13
    cle
    wbr
    @2
    @11
    @2
    @10
    chil
    wcel
    #
    @11
    cr
    wcel
    @1
    @0
    @9
    cch
    wcel
    @14
    cA
    choccl
    @9
    cS
    hstcl
    sylan2
    @10
    normcl
    syl
    #
    sqge0d
    @2
    @6
    @12
    @2
    @4
    @2
    @3
    chil
    wcel
    #
    @4
    cr
    wcel
    #
    cA
    cS
    hstcl
    #
    @3
    normcl
    syl
    #
    resqcld
    @2
    @11
    @15
    resqcld
    addge01d
    mpbid
    @2
    @13
    c1
    @7
    cA
    cS
    hstnmoc
    sq1
    syl6eqr
    breqtrd
    @2
    @17
    cc0
    @4
    cle
    wbr
    #
    @5
    @8
    wb
    #
    @19
    @2
    @16
    @20
    @18
    @3
    normge0
    syl
    @17
    @20
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @21
    1re
    0le1
    @4
    c1
    le2sq
    mpanr12
    syl2anc
    mpbird
end
