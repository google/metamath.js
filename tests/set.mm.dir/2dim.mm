include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "eqid.mm"
include "3dim1.mm"
include "df-3an.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "bitri.mm"
include "simplbi.mm"
include "cal.mm"
include "wb.mm"
include "simplll.mm"
include "hlatl.mm"
include "syl.mm"
include "simplr.mm"
include "simpllr.mm"
include "atncmp.mm"
include "syl3anc.mm"
include "necom.mm"
include "syl6rbb.mm"
include "cbs.mm"
include "atbase.mm"
include "cvr1.mm"
include "bitrd.mm"
include "hlatjcl.mm"
include "simpr.mm"
include "anbi12d.mm"
include "syl5ib.mm"
include "reximdva.mm"
include "mpd.mm"

theorem 2dim
  let cA: class A
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let vr: setvar r
  let vq: setvar q
  let vs: setvar s
  assume 2dim.j: |- .\/ = ( join ` K )
  assume 2dim.c: |- C = ( <o ` K )
  assume 2dim.a: |- A = ( Atoms ` K )

  disjoint q r
  disjoint A q
  disjoint A r
  disjoint .\/ q
  disjoint .\/ r
  disjoint K q
  disjoint K r
  disjoint P q
  disjoint P r
  disjoint q s
  disjoint r s
  disjoint A s
  disjoint .\/ s
  disjoint K s
  disjoint P s
  assert |- ( ( K e. HL /\ P e. A ) -> E. q e. A E. r e. A ( P C ( P .\/ q ) /\ ( P .\/ q ) C ( ( P .\/ q ) .\/ r ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    wa
    #
    cP
    vq
    cv
    #
    wne
    #
    vr
    cv
    #
    cP
    @3
    c.or
    co
    #
    cK
    cple
    cfv
    #
    wbr
    wn
    #
    vs
    cv
    @6
    @5
    c.or
    co
    #
    @7
    wbr
    wn
    #
    w3a
    #
    vs
    cA
    wrex
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    cP
    @6
    cC
    wbr
    #
    @6
    @9
    cC
    wbr
    #
    wa
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    cA
    cP
    c.or
    cK
    @7
    vs
    vr
    vq
    2dim.j
    @7
    eqid
    #
    2dim.a
    3dim1
    @2
    @13
    @17
    vq
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @12
    @16
    vr
    cA
    @12
    @4
    @8
    wa
    #
    @20
    @5
    cA
    wcel
    #
    wa
    #
    @16
    @12
    @21
    @10
    vs
    cA
    wrex
    #
    @12
    @21
    @10
    wa
    #
    vs
    cA
    wrex
    @21
    @24
    wa
    @11
    @25
    vs
    cA
    @4
    @8
    @10
    df-3an
    rexbii
    @21
    @10
    vs
    cA
    r19.42v
    bitri
    simplbi
    @23
    @4
    @14
    @8
    @15
    @23
    @4
    @3
    cP
    @7
    wbr
    wn
    #
    @14
    @23
    @26
    @3
    cP
    wne
    #
    @4
    @23
    cK
    cal
    wcel
    #
    @19
    @1
    @26
    @27
    wb
    @23
    @0
    @28
    @0
    @1
    @19
    @22
    simplll
    #
    cK
    hlatl
    syl
    @2
    @19
    @22
    simplr
    #
    @0
    @1
    @19
    @22
    simpllr
    #
    cA
    @3
    cP
    cK
    @7
    @18
    2dim.a
    atncmp
    syl3anc
    @3
    cP
    necom
    syl6rbb
    @23
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @19
    @26
    @14
    wb
    @29
    @23
    @1
    @33
    @31
    cA
    @32
    cP
    cK
    @32
    eqid
    #
    2dim.a
    atbase
    syl
    @30
    cA
    @32
    cC
    @3
    c.or
    cK
    @7
    cP
    @34
    @18
    2dim.j
    2dim.c
    2dim.a
    cvr1
    syl3anc
    bitrd
    @23
    @0
    @6
    @32
    wcel
    #
    @22
    @8
    @15
    wb
    @29
    @23
    @0
    @1
    @19
    @35
    @29
    @31
    @30
    cA
    @32
    c.or
    cK
    cP
    @3
    @34
    2dim.j
    2dim.a
    hlatjcl
    syl3anc
    @20
    @22
    simpr
    cA
    @32
    cC
    @5
    c.or
    cK
    @7
    @6
    @34
    @18
    2dim.j
    2dim.c
    2dim.a
    cvr1
    syl3anc
    anbi12d
    syl5ib
    reximdva
    reximdva
    mpd
end
