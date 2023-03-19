include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "0re.mm"
include "a1i.mm"
include "clt.mm"
include "wn.mm"
include "simpr.mm"
include "1red.mm"
include "adantr.mm"
include "ltnled.mm"
include "mpbird.mm"
include "cmul.mm"
include "0lt1.mm"
include "lttrd.mm"
include "elrpd.mm"
include "ltmul2dd.mm"
include "wceq.mm"
include "recnd.mm"
include "mulid1d.mm"
include "sqvald.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "mpbid.mm"
include "syldan.mm"
include "adantlr.mm"
include "resqcld.mm"
include "lenltd.mm"
include "condan.mm"
include "sqge0d.mm"
include "letrd.mm"
include "eliccd.mm"
include "ex.mm"
include "unitssre.mm"
include "sseli.mm"
include "cxr.mm"
include "0xr.mm"
include "rexrd.mm"
include "id.mm"
include "iccgelbd.mm"
include "iccleubd.mm"
include "lemul2ad.mm"
include "adantl.mm"
include "impbid.mm"

theorem sqrlearg
  let wph: wff ph
  let cA: class A
  assume sqrlearg.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( ( A ^ 2 ) <_ A <-> A e. ( 0 [,] 1 ) ) )

  proof
    wph
    cA
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    cA
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    wph
    @1
    @3
    wph
    @1
    wa
    #
    cc0
    c1
    cA
    cc0
    cr
    wcel
    #
    @4
    0re
    a1i
    #
    wph
    @1
    cA
    c1
    cle
    wbr
    #
    c1
    cr
    wcel
    @4
    @7
    cA
    @0
    clt
    wbr
    #
    wph
    @7
    wn
    #
    @8
    @1
    wph
    @9
    c1
    cA
    clt
    wbr
    #
    @8
    wph
    @9
    wa
    #
    @10
    @9
    wph
    @9
    simpr
    @11
    c1
    cA
    @11
    1red
    wph
    cA
    cr
    wcel
    #
    @9
    sqrlearg.1
    adantr
    ltnled
    mpbird
    wph
    @10
    wa
    #
    cA
    c1
    cmul
    co
    #
    cA
    cA
    cmul
    co
    #
    clt
    wbr
    @8
    @13
    c1
    cA
    cA
    @13
    1red
    #
    wph
    @12
    @10
    sqrlearg.1
    adantr
    #
    @13
    cA
    @17
    @13
    cc0
    c1
    cA
    @5
    @13
    0re
    a1i
    @16
    @17
    cc0
    c1
    clt
    wbr
    @13
    0lt1
    a1i
    wph
    @10
    simpr
    #
    lttrd
    elrpd
    @18
    ltmul2dd
    @13
    @14
    cA
    @15
    @0
    clt
    wph
    @14
    cA
    wceq
    #
    @10
    wph
    cA
    wph
    cA
    sqrlearg.1
    recnd
    #
    mulid1d
    #
    adantr
    wph
    @15
    @0
    wceq
    #
    @10
    wph
    @0
    @15
    wph
    cA
    @20
    sqvald
    eqcomd
    #
    adantr
    breq12d
    mpbid
    syldan
    adantlr
    @4
    @8
    wn
    #
    @9
    @4
    @1
    @24
    wph
    @1
    simpr
    #
    @4
    @0
    cA
    wph
    @0
    cr
    wcel
    @1
    wph
    cA
    sqrlearg.1
    resqcld
    adantr
    #
    wph
    @12
    @1
    sqrlearg.1
    adantr
    #
    lenltd
    mpbid
    adantr
    condan
    #
    wph
    @7
    wa
    1red
    syldan
    @27
    @4
    cc0
    @0
    cA
    @6
    @26
    @27
    @4
    cA
    @27
    sqge0d
    @25
    letrd
    @28
    eliccd
    ex
    wph
    @3
    @1
    wph
    @3
    wa
    #
    @15
    @14
    cle
    wbr
    #
    @1
    @3
    @30
    wph
    @3
    cA
    c1
    cA
    @2
    cr
    cA
    unitssre
    sseli
    #
    @3
    1red
    #
    @31
    @3
    cc0
    c1
    cA
    cc0
    cxr
    wcel
    @3
    0xr
    a1i
    #
    @3
    c1
    @32
    rexrd
    #
    @3
    id
    #
    iccgelbd
    @3
    cc0
    c1
    cA
    @33
    @34
    @35
    iccleubd
    lemul2ad
    adantl
    @29
    @15
    @0
    @14
    cA
    cle
    wph
    @22
    @3
    @23
    adantr
    wph
    @19
    @3
    @21
    adantr
    breq12d
    mpbid
    ex
    impbid
end
