include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wrex.mm"
include "cv.mm"
include "cio.mm"
include "eqidd.mm"
include "ancli.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylan2.mm"
include "adantl.mm"
include "cvv.mm"
include "weu.mm"
include "wb.mm"
include "csb.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "csbex.mm"
include "syl6eqelr.mm"
include "ad2antrl.mm"
include "wex.mm"
include "wal.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "spcegv.mm"
include "syl.mm"
include "adantr.mm"
include "mpd.mm"
include "r19.29.mm"
include "an4.mm"
include "pm3.35.mm"
include "eqeq12.mm"
include "syl5ibrcom.mm"
include "ancoms.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "rexlimivw.mm"
include "imp.mm"
include "sylan.mm"
include "an32s.mm"
include "ex.mm"
include "alrimivv.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "eu4.mm"
include "sylanbrc.mm"
include "iota2.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem unirep
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vw: setvar w
  assume unirep.1: |- ( y = D -> ( ph <-> ps ) )
  assume unirep.2: |- ( y = D -> B = C )
  assume unirep.3: |- ( y = z -> ( ph <-> ch ) )
  assume unirep.4: |- ( y = z -> B = F )
  assume unirep.5: |- B e. _V

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph z
  disjoint ps x
  disjoint ps y
  disjoint ch x
  disjoint ch y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C w
  disjoint D w
  disjoint F w
  disjoint ph w
  disjoint ps w
  disjoint ch w
  assert |- ( ( A. y e. A A. z e. A ( ( ph /\ ch ) -> B = F ) /\ ( D e. A /\ ps ) ) -> ( iota x E. y e. A ( ph /\ x = B ) ) = C )

  proof
    wph
    wch
    wa
    #
    cB
    cF
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    cD
    cA
    wcel
    #
    wps
    wa
    #
    wa
    #
    wph
    cC
    cB
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    wph
    vx
    cv
    #
    cB
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cio
    cC
    wceq
    #
    @6
    @10
    @4
    wps
    @5
    wps
    cC
    cC
    wceq
    #
    wa
    #
    @10
    wps
    @16
    wps
    cC
    eqidd
    ancli
    @9
    @17
    vy
    cD
    cA
    vy
    cv
    #
    cD
    wceq
    #
    wph
    wps
    @8
    @16
    unirep.1
    @19
    cB
    cC
    cC
    unirep.2
    eqeq2d
    anbi12d
    rspcev
    sylan2
    #
    adantl
    @7
    cC
    cvv
    wcel
    #
    @14
    vx
    weu
    #
    @10
    @15
    wb
    @5
    @21
    @4
    wps
    @5
    cC
    vy
    cD
    cB
    csb
    cvv
    vy
    cD
    cB
    cC
    cA
    @5
    vy
    cC
    nfcvd
    unirep.2
    csbiegf
    vy
    cD
    cB
    unirep.5
    csbex
    syl6eqelr
    #
    ad2antrl
    @7
    @14
    vx
    wex
    #
    @14
    wch
    vw
    cv
    #
    cF
    wceq
    #
    wa
    #
    vz
    cA
    wrex
    #
    wa
    @11
    @25
    wceq
    #
    wi
    #
    vw
    wal
    vx
    wal
    @22
    @6
    @24
    @4
    @6
    @10
    @24
    @20
    @5
    @10
    @24
    wi
    #
    wps
    @5
    @21
    @31
    @23
    @14
    @10
    vx
    cC
    cvv
    @11
    cC
    wceq
    #
    @13
    @9
    vy
    cA
    @32
    @12
    @8
    wph
    @11
    cC
    cB
    eqeq1
    anbi2d
    rexbidv
    #
    spcegv
    syl
    adantr
    mpd
    adantl
    @7
    @30
    vx
    vw
    @4
    @30
    @6
    @4
    @14
    @28
    @29
    @4
    @14
    wa
    @3
    @13
    wa
    #
    vy
    cA
    wrex
    @28
    @29
    wi
    #
    @3
    @13
    vy
    cA
    r19.29
    @34
    @35
    vy
    cA
    @34
    @28
    @29
    @3
    @28
    @13
    @29
    @3
    @28
    wa
    @2
    @27
    wa
    #
    vz
    cA
    wrex
    #
    @13
    @29
    @2
    @27
    vz
    cA
    r19.29
    @37
    @13
    @29
    @36
    @13
    @29
    wi
    vz
    cA
    @2
    @27
    @13
    @29
    @2
    @13
    @27
    @29
    @13
    @27
    wa
    @0
    @12
    @26
    wa
    #
    wa
    @2
    @29
    wph
    @12
    wch
    @26
    an4
    @2
    @0
    @38
    @29
    @0
    @2
    @38
    @29
    wi
    @0
    @2
    wa
    @29
    @38
    @1
    @0
    @1
    pm3.35
    @11
    cB
    @25
    cF
    eqeq12
    syl5ibrcom
    ancoms
    expimpd
    syl5bi
    ancomsd
    expdimp
    rexlimivw
    imp
    sylan
    an32s
    ex
    rexlimivw
    syl
    expimpd
    adantr
    alrimivv
    @14
    @28
    vx
    vw
    @29
    @14
    wph
    @25
    cB
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    @28
    @29
    @13
    @40
    vy
    cA
    @29
    @12
    @39
    wph
    @11
    @25
    cB
    eqeq1
    anbi2d
    rexbidv
    @40
    @27
    vy
    vz
    cA
    @18
    vz
    cv
    wceq
    #
    wph
    wch
    @39
    @26
    unirep.3
    @41
    cB
    cF
    @25
    unirep.4
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    eu4
    sylanbrc
    @14
    @10
    vx
    cC
    cvv
    @33
    iota2
    syl2anc
    mpbid
end
