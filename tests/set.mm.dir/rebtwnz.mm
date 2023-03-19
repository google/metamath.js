include "cr.mm"
include "wcel.mm"
include "cneg.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "wreu.mm"
include "renegcl.mm"
include "zbtwnre.mm"
include "syl.mm"
include "znegcl.mm"
include "cc.mm"
include "wceq.mm"
include "wb.mm"
include "zcn.mm"
include "negcon2.mm"
include "syl2an.mm"
include "reuhyp.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "reuxfr.mm"
include "zre.mm"
include "leneg.mm"
include "ancoms.mm"
include "cmin.mm"
include "peano2rem.mm"
include "ltneg.mm"
include "sylan.mm"
include "1re.mm"
include "ltsubadd.mm"
include "mp3an2.mm"
include "recn.mm"
include "ax-1cn.mm"
include "negsubdi.mm"
include "sylancl.mm"
include "adantr.mm"
include "breq2d.mm"
include "3bitr3d.mm"
include "sylan2.mm"
include "bicomd.mm"
include "reubidva.mm"
include "syl5bb.mm"
include "mpbid.mm"

theorem rebtwnz
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. RR -> E! x e. ZZ ( x <_ A /\ A < ( x + 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    vy
    cv
    #
    cle
    wbr
    #
    @2
    @1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vy
    cz
    wreu
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    cA
    @8
    c1
    caddc
    co
    clt
    wbr
    #
    wa
    #
    vx
    cz
    wreu
    #
    @0
    @1
    cr
    wcel
    @7
    cA
    renegcl
    vy
    @1
    zbtwnre
    syl
    @7
    @1
    @8
    cneg
    #
    cle
    wbr
    #
    @13
    @4
    clt
    wbr
    #
    wa
    #
    vx
    cz
    wreu
    @0
    @12
    @6
    @16
    vy
    vx
    @13
    cz
    @8
    znegcl
    vy
    vx
    @13
    @2
    cneg
    #
    cz
    @2
    znegcl
    @2
    cz
    wcel
    @2
    cc
    wcel
    @8
    cc
    wcel
    @2
    @13
    wceq
    #
    @8
    @17
    wceq
    wb
    @8
    cz
    wcel
    #
    @2
    zcn
    @8
    zcn
    @2
    @8
    negcon2
    syl2an
    reuhyp
    @18
    @3
    @14
    @5
    @15
    @2
    @13
    @1
    cle
    breq2
    @2
    @13
    @4
    clt
    breq1
    anbi12d
    reuxfr
    @0
    @16
    @11
    vx
    cz
    @0
    @19
    wa
    @11
    @16
    @19
    @0
    @8
    cr
    wcel
    #
    @11
    @16
    wb
    @8
    zre
    @0
    @20
    wa
    #
    @9
    @14
    @10
    @15
    @20
    @0
    @9
    @14
    wb
    @8
    cA
    leneg
    ancoms
    @21
    cA
    c1
    cmin
    co
    #
    @8
    clt
    wbr
    #
    @13
    @22
    cneg
    #
    clt
    wbr
    #
    @10
    @15
    @0
    @22
    cr
    wcel
    @20
    @23
    @25
    wb
    cA
    peano2rem
    @22
    @8
    ltneg
    sylan
    @0
    c1
    cr
    wcel
    @20
    @23
    @10
    wb
    1re
    cA
    c1
    @8
    ltsubadd
    mp3an2
    @21
    @24
    @4
    @13
    clt
    @0
    @24
    @4
    wceq
    #
    @20
    @0
    cA
    cc
    wcel
    c1
    cc
    wcel
    @26
    cA
    recn
    ax-1cn
    cA
    c1
    negsubdi
    sylancl
    adantr
    breq2d
    3bitr3d
    anbi12d
    sylan2
    bicomd
    reubidva
    syl5bb
    mpbid
end
