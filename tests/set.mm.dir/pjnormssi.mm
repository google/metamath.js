include "wss.mm"
include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wcel.mm"
include "cc0.mm"
include "cmv.mm"
include "co.mm"
include "csp.mm"
include "cort.mm"
include "cin.mm"
include "wceq.mm"
include "pjssmi.mm"
include "pjssge0i.mm"
include "syld.mm"
include "pjdifnormi.mm"
include "sylibd.mm"
include "com12.mm"
include "ralrimiv.mm"
include "wi.mm"
include "wal.mm"
include "choccli.mm"
include "cheli.mm"
include "wa.mm"
include "breq2.mm"
include "biimpac.mm"
include "pjhcli.mm"
include "normge0.mm"
include "syl.mm"
include "cr.mm"
include "normcl.mm"
include "0re.mm"
include "letri3.mm"
include "biimprd.mm"
include "sylancl.mm"
include "sylan2i.mm"
include "anabsi6.mm"
include "sylan2.mm"
include "expr.mm"
include "wb.mm"
include "c0v.mm"
include "norm-i.mm"
include "cch.mm"
include "pjoc2.mm"
include "mpan.mm"
include "bitr4d.mm"
include "adantr.mm"
include "3imtr3d.mm"
include "ex.mm"
include "a2i.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "alimi.mm"
include "df-ral.mm"
include "dfss2.mm"
include "3imtr4i.mm"
include "chsscon3i.mm"
include "sylibr.mm"
include "impbii.mm"

theorem pjnormssi
  let vx: setvar x
  let cG: class G
  let cH: class H
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH

  disjoint H x
  disjoint G x
  disjoint x y
  disjoint H y
  disjoint G y
  assert |- ( G C_ H <-> A. x e. ~H ( normh ` ( ( projh ` G ) ` x ) ) <_ ( normh ` ( ( projh ` H ) ` x ) ) )

  proof
    cG
    cH
    wss
    #
    vx
    cv
    #
    cG
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    @1
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @0
    @6
    vx
    chil
    @1
    chil
    wcel
    #
    @0
    @6
    @8
    @0
    cc0
    @4
    @2
    cmv
    co
    #
    @1
    csp
    co
    cle
    wbr
    #
    @6
    @8
    @0
    @9
    @1
    cH
    cG
    cort
    cfv
    #
    cin
    cpjh
    cfv
    cfv
    wceq
    @10
    @1
    cH
    cG
    pjco.2
    pjco.1
    pjssmi
    @1
    cH
    cG
    pjco.2
    pjco.1
    pjssge0i
    syld
    @1
    cH
    cG
    pjco.2
    pjco.1
    pjdifnormi
    sylibd
    com12
    ralrimiv
    @7
    cH
    cort
    cfv
    #
    @11
    wss
    #
    @0
    @8
    @6
    wi
    #
    vx
    wal
    @1
    @12
    wcel
    #
    @1
    @11
    wcel
    #
    wi
    #
    vx
    wal
    @7
    @13
    @14
    @17
    vx
    @14
    @15
    @16
    @15
    @8
    @14
    @17
    @1
    @12
    cH
    pjco.2
    choccli
    cheli
    @8
    @6
    @17
    @8
    @6
    @17
    @8
    @6
    wa
    @5
    cc0
    wceq
    #
    @3
    cc0
    wceq
    #
    @15
    @16
    @8
    @6
    @18
    @19
    @6
    @18
    wa
    @8
    @3
    cc0
    cle
    wbr
    #
    @19
    @18
    @6
    @20
    @5
    cc0
    @3
    cle
    breq2
    biimpac
    @8
    @20
    @19
    @8
    @8
    @20
    cc0
    @3
    cle
    wbr
    #
    @19
    @8
    @2
    chil
    wcel
    #
    @21
    @1
    cG
    pjco.1
    pjhcli
    #
    @2
    normge0
    syl
    @8
    @3
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @20
    @21
    wa
    #
    @19
    wi
    @8
    @22
    @24
    @23
    @2
    normcl
    syl
    0re
    @24
    @25
    wa
    @19
    @26
    @3
    cc0
    letri3
    biimprd
    sylancl
    sylan2i
    anabsi6
    sylan2
    expr
    @8
    @18
    @15
    wb
    @6
    @8
    @18
    @4
    c0v
    wceq
    #
    @15
    @8
    @4
    chil
    wcel
    @18
    @27
    wb
    @1
    cH
    pjco.2
    pjhcli
    @4
    norm-i
    syl
    cH
    cch
    wcel
    @8
    @15
    @27
    wb
    pjco.2
    @1
    cH
    pjoc2
    mpan
    bitr4d
    adantr
    @8
    @19
    @16
    wb
    @6
    @8
    @19
    @2
    c0v
    wceq
    #
    @16
    @8
    @22
    @19
    @28
    wb
    @23
    @2
    norm-i
    syl
    cG
    cch
    wcel
    @8
    @16
    @28
    wb
    pjco.1
    @1
    cG
    pjoc2
    mpan
    bitr4d
    adantr
    3imtr3d
    ex
    a2i
    syl5
    pm2.43d
    alimi
    @6
    vx
    chil
    df-ral
    vx
    @12
    @11
    dfss2
    3imtr4i
    cG
    cH
    pjco.1
    pjco.2
    chsscon3i
    sylibr
    impbii
end
