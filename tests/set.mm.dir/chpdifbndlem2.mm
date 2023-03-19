include "crp.mm"
include "wcel.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "clog.mm"
include "cdiv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "wral.mm"
include "c1.mm"
include "cpnf.mm"
include "cioo.mm"
include "wrex.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "sylancl.mm"
include "rpmulcld.mm"
include "rpred.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "sylancr.mm"
include "relogcld.mm"
include "remulcld.mm"
include "readdcld.mm"
include "cc0.mm"
include "clt.mm"
include "00id.mm"
include "0red.mm"
include "rpgt0d.mm"
include "cr.mm"
include "wa.mm"
include "rprege0d.mm"
include "log1.mm"
include "wb.mm"
include "logleb.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "mulge0.mm"
include "syl12anc.mm"
include "ltleaddd.mm"
include "elrpd.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "csu.mm"
include "cabs.mm"
include "cico.mm"
include "simprl.mm"
include "simprr.mm"
include "chpdifbndlem1.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem chpdifbndlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vc: setvar c
  let vn: setvar n
  let cX: class X
  let cY: class Y
  assume chpdifbnd.a: |- ( ph -> A e. RR+ )
  assume chpdifbnd.1: |- ( ph -> 1 <_ A )
  assume chpdifbnd.b: |- ( ph -> B e. RR+ )
  assume chpdifbnd.2: |- ( ph -> A. z e. ( 1 [,) +oo ) ( abs ` ( ( ( ( ( psi ` z ) x. ( log ` z ) ) + sum_ m e. ( 1 ... ( |_ ` z ) ) ( ( Lam ` m ) x. ( psi ` ( z / m ) ) ) ) / z ) - ( 2 x. ( log ` z ) ) ) ) <_ B )
  assume chpdifbnd.c: |- C = ( ( B x. ( A + 1 ) ) + ( ( 2 x. A ) x. ( log ` A ) ) )

  disjoint c m
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint C c
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint A c
  disjoint B z
  disjoint c n
  disjoint m n
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint C n
  disjoint n ph
  disjoint X n
  disjoint X z
  disjoint Y n
  disjoint Y z
  assert |- ( ph -> E. c e. RR+ A. x e. ( 1 (,) +oo ) A. y e. ( x [,] ( A x. x ) ) ( ( psi ` y ) - ( psi ` x ) ) <_ ( ( 2 x. ( y - x ) ) + ( c x. ( x / ( log ` x ) ) ) ) )

  proof
    wph
    cC
    crp
    wcel
    vy
    cv
    #
    cchp
    cfv
    vx
    cv
    #
    cchp
    cfv
    cmin
    co
    #
    c2
    @0
    @1
    cmin
    co
    cmul
    co
    #
    cC
    @1
    @1
    clog
    cfv
    cdiv
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    @1
    cA
    @1
    cmul
    co
    cicc
    co
    #
    wral
    vx
    c1
    cpnf
    cioo
    co
    #
    wral
    #
    @2
    @3
    vc
    cv
    #
    @4
    cmul
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    @8
    wral
    vx
    @9
    wral
    #
    vc
    crp
    wrex
    wph
    cC
    cB
    cA
    c1
    caddc
    co
    #
    cmul
    co
    #
    c2
    cA
    cmul
    co
    #
    cA
    clog
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    crp
    chpdifbnd.c
    wph
    @21
    wph
    @17
    @20
    wph
    @17
    wph
    cB
    @16
    chpdifbnd.b
    wph
    cA
    crp
    wcel
    #
    c1
    crp
    wcel
    #
    @16
    crp
    wcel
    chpdifbnd.a
    1rp
    cA
    c1
    rpaddcl
    sylancl
    rpmulcld
    #
    rpred
    #
    wph
    @18
    @19
    wph
    @18
    wph
    c2
    crp
    wcel
    @22
    @18
    crp
    wcel
    2rp
    chpdifbnd.a
    c2
    cA
    rpmulcl
    sylancr
    #
    rpred
    wph
    cA
    chpdifbnd.a
    relogcld
    #
    remulcld
    #
    readdcld
    wph
    cc0
    cc0
    cc0
    caddc
    co
    @21
    clt
    00id
    wph
    cc0
    cc0
    @17
    @20
    wph
    0red
    #
    @29
    @25
    @28
    wph
    @17
    @24
    rpgt0d
    wph
    @18
    cr
    wcel
    cc0
    @18
    cle
    wbr
    wa
    @19
    cr
    wcel
    cc0
    @19
    cle
    wbr
    cc0
    @20
    cle
    wbr
    wph
    @18
    @26
    rprege0d
    @27
    wph
    cc0
    c1
    clog
    cfv
    #
    @19
    cle
    log1
    wph
    c1
    cA
    cle
    wbr
    #
    @30
    @19
    cle
    wbr
    #
    chpdifbnd.1
    wph
    @23
    @22
    @31
    @32
    wb
    1rp
    chpdifbnd.a
    c1
    cA
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @18
    @19
    mulge0
    syl12anc
    ltleaddd
    syl5eqbrr
    elrpd
    syl5eqel
    wph
    @7
    vx
    vy
    @9
    @8
    wph
    @1
    @9
    wcel
    #
    @0
    @8
    wcel
    #
    wa
    #
    wa
    vz
    cA
    cB
    cC
    vm
    @1
    @0
    wph
    @22
    @35
    chpdifbnd.a
    adantr
    wph
    @31
    @35
    chpdifbnd.1
    adantr
    wph
    cB
    crp
    wcel
    @35
    chpdifbnd.b
    adantr
    wph
    vz
    cv
    #
    cchp
    cfv
    @36
    clog
    cfv
    #
    cmul
    co
    c1
    @36
    cfl
    cfv
    cfz
    co
    vm
    cv
    #
    cvma
    cfv
    @36
    @38
    cdiv
    co
    cchp
    cfv
    cmul
    co
    vm
    csu
    caddc
    co
    @36
    cdiv
    co
    c2
    @37
    cmul
    co
    cmin
    co
    cabs
    cfv
    cB
    cle
    wbr
    vz
    c1
    cpnf
    cico
    co
    wral
    @35
    chpdifbnd.2
    adantr
    chpdifbnd.c
    wph
    @33
    @34
    simprl
    wph
    @33
    @34
    simprr
    chpdifbndlem1
    ralrimivva
    @15
    @10
    vc
    cC
    crp
    @11
    cC
    wceq
    #
    @14
    @7
    vx
    vy
    @9
    @8
    @39
    @13
    @6
    @2
    cle
    @39
    @12
    @5
    @3
    caddc
    @11
    cC
    @4
    cmul
    oveq1
    oveq2d
    breq2d
    2ralbidv
    rspcev
    syl2anc
end
