include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "dnibndlem12.mm"
include "eqcomd.mm"
include "dnibndlem9.mm"
include "wo.mm"
include "cz.mm"
include "wb.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "flcld.mm"
include "jca.mm"
include "adantr.mm"
include "zltp1le.mm"
include "syl.mm"
include "mpbid.mm"
include "reflcl.mm"
include "peano2re.mm"
include "zred.mm"
include "leloed.mm"
include "wi.mm"
include "peano2zd.mm"
include "recnd.mm"
include "1cnd.mm"
include "addassd.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "bitrd.mm"
include "biimpd.mm"
include "orim1d.mm"
include "mpd.mm"
include "mpjaodan.mm"
include "dnibndlem2.mm"

theorem dnibndlem13
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibndlem13.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem13.2: |- ( ph -> A e. RR )
  assume dnibndlem13.3: |- ( ph -> B e. RR )
  assume dnibndlem13.4: |- ( ph -> ( |_ ` ( A + ( 1 / 2 ) ) ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cA
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cB
    @0
    caddc
    co
    #
    cfl
    cfv
    #
    clt
    wbr
    #
    cB
    cT
    cfv
    cA
    cT
    cfv
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    cabs
    cfv
    cle
    wbr
    #
    @2
    @4
    wceq
    #
    wph
    @5
    wa
    #
    @2
    c2
    caddc
    co
    #
    @4
    cle
    wbr
    #
    @6
    @2
    c1
    caddc
    co
    #
    @4
    wceq
    #
    @8
    @10
    wa
    vx
    cA
    cB
    cT
    dnibndlem13.1
    wph
    cA
    cr
    wcel
    #
    @5
    @10
    dnibndlem13.2
    ad2antrr
    wph
    cB
    cr
    wcel
    #
    @5
    @10
    dnibndlem13.3
    ad2antrr
    @8
    @10
    simpr
    dnibndlem12
    @8
    @12
    wa
    #
    vx
    cA
    cB
    cT
    dnibndlem13.1
    wph
    @13
    @5
    @12
    dnibndlem13.2
    ad2antrr
    wph
    @14
    @5
    @12
    dnibndlem13.3
    ad2antrr
    @15
    @11
    @4
    @8
    @12
    simpr
    eqcomd
    dnibndlem9
    @8
    @11
    @4
    clt
    wbr
    #
    @12
    wo
    #
    @10
    @12
    wo
    @8
    @11
    @4
    cle
    wbr
    #
    @17
    @8
    @5
    @18
    wph
    @5
    simpr
    @8
    @2
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    wa
    #
    @5
    @18
    wb
    wph
    @21
    @5
    wph
    @19
    @20
    wph
    @1
    wph
    cA
    @0
    dnibndlem13.2
    @0
    cr
    wcel
    wph
    halfre
    a1i
    #
    readdcld
    #
    flcld
    #
    wph
    @3
    wph
    cB
    @0
    dnibndlem13.3
    @22
    readdcld
    flcld
    #
    jca
    adantr
    @2
    @4
    zltp1le
    syl
    mpbid
    @8
    @11
    @4
    wph
    @11
    cr
    wcel
    #
    @5
    wph
    @2
    cr
    wcel
    #
    @26
    wph
    @1
    cr
    wcel
    @27
    @23
    @1
    reflcl
    syl
    #
    @2
    peano2re
    syl
    adantr
    wph
    @4
    cr
    wcel
    @5
    wph
    @4
    @25
    zred
    #
    adantr
    leloed
    mpbid
    @8
    @16
    @10
    @12
    wph
    @16
    @10
    wi
    @5
    wph
    @16
    @10
    wph
    @16
    @11
    c1
    caddc
    co
    #
    @4
    cle
    wbr
    #
    @10
    wph
    @11
    cz
    wcel
    #
    @20
    wa
    @16
    @31
    wb
    wph
    @32
    @20
    wph
    @2
    @24
    peano2zd
    @25
    jca
    @11
    @4
    zltp1le
    syl
    wph
    @30
    @9
    @4
    cle
    wph
    @30
    @2
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @9
    wph
    @2
    c1
    c1
    wph
    @2
    @28
    recnd
    wph
    1cnd
    #
    @34
    addassd
    wph
    @33
    c2
    @2
    caddc
    @33
    c2
    wceq
    wph
    1p1e2
    a1i
    oveq2d
    eqtrd
    breq1d
    bitrd
    biimpd
    adantr
    orim1d
    mpd
    mpjaodan
    wph
    @7
    wa
    #
    vx
    cA
    cB
    cT
    dnibndlem13.1
    wph
    @13
    @7
    dnibndlem13.2
    adantr
    wph
    @14
    @7
    dnibndlem13.3
    adantr
    @35
    @2
    @4
    wph
    @7
    simpr
    eqcomd
    dnibndlem2
    wph
    @2
    @4
    cle
    wbr
    @5
    @7
    wo
    dnibndlem13.4
    wph
    @2
    @4
    @28
    @29
    leloed
    mpbid
    mpjaodan
end
