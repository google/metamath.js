include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cmo.mm"
include "clt.mm"
include "wceq.mm"
include "cn.mm"
include "wb.mm"
include "eldifi.mm"
include "adantl.mm"
include "simpl.mm"
include "oddprm.mm"
include "prmdvdsexp.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "prmgt1.mm"
include "syl.mm"
include "ad2antlr.mm"
include "p1modz1.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "cc0.mm"
include "1m1e0.mm"
include "cneg.mm"
include "lgslem2.mm"
include "simp2i.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "wn.mm"
include "w3a.mm"
include "cpr.mm"
include "wo.mm"
include "lgslem1.mm"
include "elpri.mm"
include "oveq1.mm"
include "df-neg.mm"
include "simp1i.mm"
include "eqeltrri.mm"
include "2m1e1.mm"
include "simp3i.mm"
include "jaoi.mm"
include "3syl.mm"
include "3expa.mm"
include "pm2.61dan.mm"

theorem lgslem4
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cZ: class Z
  let cB: class B
  assume lgslem2.z: |- Z = { x e. ZZ | ( abs ` x ) <_ 1 }

  disjoint A x
  disjoint B x
  assert |- ( ( A e. ZZ /\ P e. ( Prime \ { 2 } ) ) -> ( ( ( ( A ^ ( ( P - 1 ) / 2 ) ) + 1 ) mod P ) - 1 ) e. Z )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cP
    cA
    cdvds
    wbr
    #
    cA
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    cP
    cmo
    co
    #
    c1
    cmin
    co
    #
    cZ
    wcel
    #
    @3
    @4
    wa
    #
    @8
    c1
    c1
    cmin
    co
    #
    cZ
    @10
    @7
    c1
    c1
    cmin
    @10
    cP
    @6
    cdvds
    wbr
    #
    c1
    cP
    clt
    wbr
    #
    @7
    c1
    wceq
    @3
    @12
    @4
    @3
    cP
    cprime
    wcel
    #
    @0
    @5
    cn
    wcel
    #
    @12
    @4
    wb
    @2
    @14
    @0
    cP
    cprime
    @1
    eldifi
    #
    adantl
    @0
    @2
    simpl
    @2
    @15
    @0
    cP
    oddprm
    adantl
    cA
    cP
    @5
    prmdvdsexp
    syl3anc
    biimpar
    @2
    @13
    @0
    @4
    @2
    @14
    @13
    @16
    cP
    prmgt1
    syl
    ad2antlr
    @6
    cP
    p1modz1
    syl2anc
    oveq1d
    @11
    cc0
    cZ
    1m1e0
    c1
    cneg
    #
    cZ
    wcel
    #
    cc0
    cZ
    wcel
    #
    c1
    cZ
    wcel
    #
    vx
    cZ
    lgslem2.z
    lgslem2
    #
    simp2i
    eqeltri
    syl6eqel
    @0
    @2
    @4
    wn
    #
    @9
    @0
    @2
    @22
    w3a
    @7
    cc0
    c2
    cpr
    wcel
    @7
    cc0
    wceq
    #
    @7
    c2
    wceq
    #
    wo
    @9
    cA
    cP
    lgslem1
    @7
    cc0
    c2
    elpri
    @23
    @9
    @24
    @23
    @8
    cc0
    c1
    cmin
    co
    #
    cZ
    @7
    cc0
    c1
    cmin
    oveq1
    @17
    @25
    cZ
    c1
    df-neg
    @18
    @19
    @20
    @21
    simp1i
    eqeltrri
    syl6eqel
    @24
    @8
    c2
    c1
    cmin
    co
    #
    cZ
    @7
    c2
    c1
    cmin
    oveq1
    @26
    c1
    cZ
    2m1e1
    @18
    @19
    @20
    @21
    simp3i
    eqeltri
    syl6eqel
    jaoi
    3syl
    3expa
    pm2.61dan
end
