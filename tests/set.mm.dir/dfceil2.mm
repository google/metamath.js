include "cceil.mm"
include "cr.mm"
include "cv.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "cmpt.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wa.mm"
include "cz.mm"
include "crio.mm"
include "df-ceil.mm"
include "wcel.mm"
include "wb.mm"
include "zre.mm"
include "lenegcon2.mm"
include "peano2re.mm"
include "anim2i.mm"
include "ancoms.mm"
include "ltnegcon1.mm"
include "syl.mm"
include "wceq.mm"
include "recn.mm"
include "1cnd.mm"
include "negdid.mm"
include "adantr.mm"
include "breq1d.mm"
include "cmin.mm"
include "renegcl.mm"
include "neg1rr.mm"
include "a1i.mm"
include "simpr.mm"
include "ltaddsubd.mm"
include "subnegd.mm"
include "adantl.mm"
include "breq2d.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "anbi12d.mm"
include "sylan2.mm"
include "riotabidva.mm"
include "negeqd.mm"
include "wreu.mm"
include "zbtwnre.mm"
include "breq2.mm"
include "breq1.mm"
include "zriotaneg.mm"
include "flval.mm"
include "3eqtr4rd.mm"
include "mpteq2ia.mm"
include "eqtri.mm"

theorem dfceil2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- |^ = ( x e. RR |-> ( iota_ y e. ZZ ( x <_ y /\ y < ( x + 1 ) ) ) )

  proof
    cceil
    vx
    cr
    vx
    cv
    #
    cneg
    #
    cfl
    cfv
    #
    cneg
    #
    cmpt
    vx
    cr
    @0
    vy
    cv
    #
    cle
    wbr
    #
    @4
    @0
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
    crio
    #
    cmpt
    vx
    df-ceil
    vx
    cr
    @3
    @9
    @0
    cr
    wcel
    #
    @0
    vz
    cv
    #
    cneg
    #
    cle
    wbr
    #
    @12
    @6
    clt
    wbr
    #
    wa
    #
    vz
    cz
    crio
    #
    cneg
    #
    @11
    @1
    cle
    wbr
    #
    @1
    @11
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vz
    cz
    crio
    #
    cneg
    @9
    @3
    @10
    @16
    @22
    @10
    @15
    @21
    vz
    cz
    @11
    cz
    wcel
    @10
    @11
    cr
    wcel
    #
    @15
    @21
    wb
    @11
    zre
    @10
    @23
    wa
    #
    @13
    @18
    @14
    @20
    @0
    @11
    lenegcon2
    @24
    @14
    @6
    cneg
    #
    @11
    clt
    wbr
    #
    @1
    c1
    cneg
    #
    caddc
    co
    #
    @11
    clt
    wbr
    #
    @20
    @24
    @23
    @6
    cr
    wcel
    #
    wa
    #
    @14
    @26
    wb
    @23
    @10
    @31
    @10
    @30
    @23
    @0
    peano2re
    anim2i
    ancoms
    @11
    @6
    ltnegcon1
    syl
    @24
    @25
    @28
    @11
    clt
    @10
    @25
    @28
    wceq
    @23
    @10
    @0
    c1
    @0
    recn
    @10
    1cnd
    negdid
    adantr
    breq1d
    @24
    @29
    @1
    @11
    @27
    cmin
    co
    #
    clt
    wbr
    @20
    @24
    @1
    @27
    @11
    @10
    @1
    cr
    wcel
    #
    @23
    @0
    renegcl
    #
    adantr
    @27
    cr
    wcel
    @24
    neg1rr
    a1i
    @10
    @23
    simpr
    ltaddsubd
    @24
    @32
    @19
    @1
    clt
    @23
    @32
    @19
    wceq
    @10
    @23
    @11
    c1
    @11
    recn
    @23
    1cnd
    subnegd
    adantl
    breq2d
    bitrd
    3bitrd
    anbi12d
    sylan2
    riotabidva
    negeqd
    @10
    @8
    vy
    cz
    wreu
    @9
    @17
    wceq
    vy
    @0
    zbtwnre
    @8
    @15
    vy
    vz
    @4
    @12
    wceq
    @5
    @13
    @7
    @14
    @4
    @12
    @0
    cle
    breq2
    @4
    @12
    @6
    clt
    breq1
    anbi12d
    zriotaneg
    syl
    @10
    @2
    @22
    @10
    @33
    @2
    @22
    wceq
    @34
    vz
    @1
    flval
    syl
    negeqd
    3eqtr4rd
    mpteq2ia
    eqtri
end
