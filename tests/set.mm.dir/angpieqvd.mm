include "cmin.mm"
include "co.mm"
include "cpi.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "cc0.mm"
include "cioo.mm"
include "wrex.mm"
include "wa.mm"
include "cdiv.mm"
include "wcel.mm"
include "cneg.mm"
include "crp.mm"
include "angpieqvdlem2.mm"
include "biimpar.mm"
include "cc.mm"
include "adantr.mm"
include "wne.mm"
include "angpined.mm"
include "imp.mm"
include "angpieqvdlem.mm"
include "mpbid.mm"
include "subcld.mm"
include "necomd.mm"
include "subne0d.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "divcld.mm"
include "affineequiv.mm"
include "mpbird.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "cr.mm"
include "simpr.mm"
include "elioore.mm"
include "recn.mm"
include "3syl.mm"
include "w3a.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "3adant3.mm"
include "eqnetrrd.mm"
include "mulne0bbd.mm"
include "divmul3d.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "subne0ad.mm"
include "3expia.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem angpieqvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume angpieqvd.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume angpieqvd.A: |- ( ph -> A e. CC )
  assume angpieqvd.B: |- ( ph -> B e. CC )
  assume angpieqvd.C: |- ( ph -> C e. CC )
  assume angpieqvd.AneB: |- ( ph -> A =/= B )
  assume angpieqvd.BneC: |- ( ph -> B =/= C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F w
  disjoint ph w
  disjoint A w
  disjoint B w
  disjoint C w
  assert |- ( ph -> ( ( ( A - B ) F ( C - B ) ) = _pi <-> E. w e. ( 0 (,) 1 ) B = ( ( w x. A ) + ( ( 1 - w ) x. C ) ) ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    cF
    co
    cpi
    wceq
    #
    cB
    vw
    cv
    #
    cA
    cmul
    co
    #
    c1
    @3
    cmin
    co
    #
    cC
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vw
    cc0
    c1
    cioo
    co
    #
    wrex
    #
    wph
    @2
    @10
    wph
    @2
    wa
    #
    @1
    cC
    cA
    cmin
    co
    #
    cdiv
    co
    #
    @9
    wcel
    #
    cB
    @13
    cA
    cmul
    co
    #
    c1
    @13
    cmin
    co
    #
    cC
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @10
    @11
    @1
    @0
    cdiv
    co
    cneg
    crp
    wcel
    #
    @14
    wph
    @20
    @2
    wph
    vx
    vy
    cA
    cB
    cC
    cF
    angpieqvd.angdef
    angpieqvd.A
    angpieqvd.B
    angpieqvd.C
    angpieqvd.AneB
    angpieqvd.BneC
    angpieqvdlem2
    biimpar
    @11
    cA
    cB
    cC
    wph
    cA
    cc
    wcel
    #
    @2
    angpieqvd.A
    adantr
    #
    wph
    cB
    cc
    wcel
    #
    @2
    angpieqvd.B
    adantr
    #
    wph
    cC
    cc
    wcel
    #
    @2
    angpieqvd.C
    adantr
    #
    wph
    cA
    cB
    wne
    #
    @2
    angpieqvd.AneB
    adantr
    wph
    @2
    cA
    cC
    wne
    wph
    vx
    vy
    cA
    cB
    cC
    cF
    angpieqvd.angdef
    angpieqvd.A
    angpieqvd.B
    angpieqvd.C
    angpieqvd.AneB
    angpieqvd.BneC
    angpined
    imp
    #
    angpieqvdlem
    mpbid
    @11
    @19
    @1
    @13
    @12
    cmul
    co
    #
    wceq
    @11
    @29
    @1
    @11
    @1
    @12
    wph
    @1
    cc
    wcel
    #
    @2
    wph
    cC
    cB
    angpieqvd.C
    angpieqvd.B
    subcld
    #
    adantr
    #
    wph
    @12
    cc
    wcel
    #
    @2
    wph
    cC
    cA
    angpieqvd.C
    angpieqvd.A
    subcld
    #
    adantr
    #
    @11
    cC
    cA
    @26
    @22
    @11
    cA
    cC
    @28
    necomd
    subne0d
    #
    divcan1d
    eqcomd
    @11
    cA
    cB
    cC
    @13
    @22
    @24
    @26
    @11
    @1
    @12
    @32
    @35
    @36
    divcld
    affineequiv
    mpbird
    @8
    @19
    vw
    @13
    @9
    @3
    @13
    wceq
    #
    @7
    @18
    cB
    @37
    @4
    @15
    @6
    @17
    caddc
    @3
    @13
    cA
    cmul
    oveq1
    @37
    @5
    @16
    cC
    cmul
    @3
    @13
    c1
    cmin
    oveq2
    oveq1d
    oveq12d
    eqeq2d
    rspcev
    syl2anc
    ex
    wph
    @8
    @2
    vw
    @9
    wph
    @3
    @9
    wcel
    #
    wa
    #
    @8
    @1
    @3
    @12
    cmul
    co
    #
    wceq
    #
    @2
    @39
    cA
    cB
    cC
    @3
    wph
    @21
    @38
    angpieqvd.A
    adantr
    wph
    @23
    @38
    angpieqvd.B
    adantr
    wph
    @25
    @38
    angpieqvd.C
    adantr
    @39
    @38
    @3
    cr
    wcel
    @3
    cc
    wcel
    #
    wph
    @38
    simpr
    @3
    cc0
    c1
    elioore
    @3
    recn
    3syl
    #
    affineequiv
    wph
    @38
    @41
    @2
    wph
    @38
    @41
    w3a
    #
    @20
    @2
    @44
    @20
    @14
    @44
    @13
    @3
    @9
    @44
    @13
    @3
    wceq
    @41
    wph
    @38
    @41
    simp3
    #
    @44
    @1
    @3
    @12
    wph
    @38
    @30
    @41
    @31
    3ad2ant1
    wph
    @38
    @42
    @41
    @43
    3adant3
    #
    wph
    @38
    @33
    @41
    @34
    3ad2ant1
    #
    @44
    @3
    @12
    @46
    @47
    @44
    @1
    @40
    cc0
    @45
    wph
    @38
    @1
    cc0
    wne
    @41
    wph
    cC
    cB
    angpieqvd.C
    angpieqvd.B
    wph
    cB
    cC
    angpieqvd.BneC
    necomd
    subne0d
    3ad2ant1
    eqnetrrd
    mulne0bbd
    #
    divmul3d
    mpbird
    wph
    @38
    @41
    simp2
    eqeltrd
    @44
    cA
    cB
    cC
    wph
    @38
    @21
    @41
    angpieqvd.A
    3ad2ant1
    #
    wph
    @38
    @23
    @41
    angpieqvd.B
    3ad2ant1
    #
    wph
    @38
    @25
    @41
    angpieqvd.C
    3ad2ant1
    #
    wph
    @38
    @27
    @41
    angpieqvd.AneB
    3ad2ant1
    #
    @44
    cC
    cA
    @44
    cC
    cA
    @51
    @49
    @48
    subne0ad
    necomd
    angpieqvdlem
    mpbird
    @44
    vx
    vy
    cA
    cB
    cC
    cF
    angpieqvd.angdef
    @49
    @50
    @51
    @52
    wph
    @38
    cB
    cC
    wne
    @41
    angpieqvd.BneC
    3ad2ant1
    angpieqvdlem2
    mpbid
    3expia
    sylbid
    rexlimdva
    impbid
end
