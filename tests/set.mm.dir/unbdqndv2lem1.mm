include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "cdiv.mm"
include "c2.mm"
include "clt.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "subcld.mm"
include "absdivd.mm"
include "adantr.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "abscld.mm"
include "readdcld.mm"
include "2re.mm"
include "a1i.mm"
include "rpred.mm"
include "remulcld.mm"
include "abs3difd.mm"
include "abssubd.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "pm2.45.mm"
include "adantl.mm"
include "wb.mm"
include "ltnled.mm"
include "mpbird.mm"
include "pm2.46.mm"
include "lt2addd.mm"
include "recnd.mm"
include "2timesd.mm"
include "eqcomd.mm"
include "mulassd.mm"
include "eqtrd.mm"
include "lelttrd.mm"
include "cc0.mm"
include "w3a.mm"
include "wne.mm"
include "cc.mm"
include "absgt0.mm"
include "syl.mm"
include "mpbid.mm"
include "jca.mm"
include "3jca.mm"
include "ltdivmul2.mm"
include "eqbrtrd.mm"
include "divcld.mm"
include "lenltd.mm"
include "condan.mm"

theorem unbdqndv2lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume unbdqndv2lem1.a: |- ( ph -> A e. CC )
  assume unbdqndv2lem1.b: |- ( ph -> B e. CC )
  assume unbdqndv2lem1.c: |- ( ph -> C e. CC )
  assume unbdqndv2lem1.d: |- ( ph -> D e. CC )
  assume unbdqndv2lem1.e: |- ( ph -> E e. RR+ )
  assume unbdqndv2lem1.1: |- ( ph -> D =/= 0 )
  assume unbdqndv2lem1.2: |- ( ph -> ( 2 x. E ) <_ ( abs ` ( ( A - B ) / D ) ) )


  assert |- ( ph -> ( ( E x. ( abs ` D ) ) <_ ( abs ` ( A - C ) ) \/ ( E x. ( abs ` D ) ) <_ ( abs ` ( B - C ) ) ) )

  proof
    wph
    cE
    cD
    cabs
    cfv
    #
    cmul
    co
    #
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @1
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wo
    #
    cA
    cB
    cmin
    co
    #
    cD
    cdiv
    co
    #
    cabs
    cfv
    #
    c2
    cE
    cmul
    co
    #
    clt
    wbr
    #
    wph
    @8
    wn
    #
    wa
    #
    @11
    @9
    cabs
    cfv
    #
    @0
    cdiv
    co
    #
    @12
    clt
    wph
    @11
    @17
    wceq
    @14
    wph
    @9
    cD
    wph
    cA
    cB
    unbdqndv2lem1.a
    unbdqndv2lem1.b
    subcld
    #
    unbdqndv2lem1.d
    unbdqndv2lem1.1
    absdivd
    adantr
    @15
    @17
    @12
    clt
    wbr
    #
    @16
    @12
    @0
    cmul
    co
    #
    clt
    wbr
    #
    @15
    @16
    @3
    @6
    caddc
    co
    #
    @20
    wph
    @16
    cr
    wcel
    #
    @14
    wph
    @9
    @18
    abscld
    #
    adantr
    wph
    @22
    cr
    wcel
    @14
    wph
    @3
    @6
    wph
    @2
    wph
    cA
    cC
    unbdqndv2lem1.a
    unbdqndv2lem1.c
    subcld
    abscld
    #
    wph
    @5
    wph
    cB
    cC
    unbdqndv2lem1.b
    unbdqndv2lem1.c
    subcld
    abscld
    #
    readdcld
    adantr
    wph
    @20
    cr
    wcel
    @14
    wph
    @12
    @0
    wph
    c2
    cE
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cE
    unbdqndv2lem1.e
    rpred
    #
    remulcld
    #
    wph
    cD
    unbdqndv2lem1.d
    abscld
    #
    remulcld
    adantr
    wph
    @16
    @22
    cle
    wbr
    @14
    wph
    @16
    @3
    cC
    cB
    cmin
    co
    cabs
    cfv
    #
    caddc
    co
    @22
    cle
    wph
    cA
    cB
    cC
    unbdqndv2lem1.a
    unbdqndv2lem1.b
    unbdqndv2lem1.c
    abs3difd
    wph
    @31
    @6
    @3
    caddc
    wph
    cC
    cB
    unbdqndv2lem1.c
    unbdqndv2lem1.b
    abssubd
    oveq2d
    breqtrd
    adantr
    @15
    @22
    @1
    @1
    caddc
    co
    #
    @20
    clt
    @15
    @3
    @6
    @1
    @1
    wph
    @3
    cr
    wcel
    @14
    @25
    adantr
    wph
    @6
    cr
    wcel
    @14
    @26
    adantr
    wph
    @1
    cr
    wcel
    @14
    wph
    cE
    @0
    @28
    @30
    remulcld
    #
    adantr
    #
    @34
    @15
    @3
    @1
    clt
    wbr
    #
    @4
    wn
    #
    @14
    @36
    wph
    @4
    @7
    pm2.45
    adantl
    wph
    @35
    @36
    wb
    @14
    wph
    @3
    @1
    @25
    @33
    ltnled
    adantr
    mpbird
    @15
    @6
    @1
    clt
    wbr
    #
    @7
    wn
    #
    @14
    @38
    wph
    @4
    @7
    pm2.46
    adantl
    wph
    @37
    @38
    wb
    @14
    wph
    @6
    @1
    @26
    @33
    ltnled
    adantr
    mpbird
    lt2addd
    wph
    @32
    @20
    wceq
    @14
    wph
    @32
    c2
    @1
    cmul
    co
    #
    @20
    wph
    @39
    @32
    wph
    @1
    wph
    @1
    @33
    recnd
    2timesd
    eqcomd
    wph
    @20
    @39
    wph
    c2
    cE
    @0
    wph
    c2
    @27
    recnd
    wph
    cE
    @28
    recnd
    wph
    @0
    @30
    recnd
    mulassd
    eqcomd
    eqtrd
    adantr
    breqtrd
    lelttrd
    wph
    @19
    @21
    wb
    #
    @14
    wph
    @23
    @12
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    cc0
    @0
    clt
    wbr
    #
    wa
    #
    w3a
    @40
    wph
    @23
    @41
    @44
    @24
    @29
    wph
    @42
    @43
    @30
    wph
    cD
    cc0
    wne
    #
    @43
    unbdqndv2lem1.1
    wph
    cD
    cc
    wcel
    @45
    @43
    wb
    unbdqndv2lem1.d
    cD
    absgt0
    syl
    mpbid
    jca
    3jca
    @16
    @12
    @0
    ltdivmul2
    syl
    adantr
    mpbird
    eqbrtrd
    wph
    @13
    wn
    #
    @14
    wph
    @12
    @11
    cle
    wbr
    @46
    unbdqndv2lem1.2
    wph
    @12
    @11
    @29
    wph
    @10
    wph
    @9
    cD
    @18
    unbdqndv2lem1.d
    unbdqndv2lem1.1
    divcld
    abscld
    lenltd
    mpbid
    adantr
    condan
end
