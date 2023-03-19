include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cmpt.mm"
include "csupp.mm"
include "wss.mm"
include "wi.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cv.mm"
include "wne.mm"
include "elex.mm"
include "syl.mm"
include "adantll.mm"
include "adantr.mm"
include "eldifsni.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "syl5.mm"
include "imp.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ss2rabdv.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "mptsuppdifd.mm"
include "3sstr4d.mm"
include "sstrd.mm"
include "wn.mm"
include "c0.mm"
include "mptexg.mm"
include "cdm.mm"
include "ovex.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "dmexg.mm"
include "syl5eqelr.mm"
include "impbii.mm"
include "anbi1i.mm"
include "supp0prc.mm"
include "sylnbi.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem suppssov1
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cL: class L
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume suppssov1.s: |- ( ph -> ( ( x e. D |-> A ) supp Y ) C_ L )
  assume suppssov1.o: |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z )
  assume suppssov1.a: |- ( ( ph /\ x e. D ) -> A e. V )
  assume suppssov1.b: |- ( ( ph /\ x e. D ) -> B e. R )
  assume suppssov1.y: |- ( ph -> Y e. W )

  disjoint ph v
  disjoint ph x
  disjoint B v
  disjoint D x
  disjoint O v
  disjoint R v
  disjoint Y v
  disjoint Y x
  disjoint Z v
  disjoint Z x
  assert |- ( ph -> ( ( x e. D |-> ( A O B ) ) supp Z ) C_ L )

  proof
    cD
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    wph
    vx
    cD
    cA
    cB
    cO
    co
    #
    cmpt
    #
    cZ
    csupp
    co
    #
    cL
    wss
    #
    wi
    @2
    wph
    @6
    @2
    wph
    wa
    #
    @5
    vx
    cD
    cA
    cmpt
    #
    cY
    csupp
    co
    #
    cL
    @7
    @3
    cvv
    cZ
    csn
    cdif
    wcel
    #
    vx
    cD
    crab
    cA
    cvv
    cY
    csn
    cdif
    wcel
    #
    vx
    cD
    crab
    @5
    @9
    @7
    @10
    @11
    vx
    cD
    @7
    vx
    cv
    cD
    wcel
    #
    wa
    #
    @10
    @11
    @13
    @10
    wa
    cA
    cvv
    wcel
    #
    cA
    cY
    wne
    #
    @11
    @13
    @14
    @10
    wph
    @12
    @14
    @2
    wph
    @12
    wa
    cA
    cV
    wcel
    @14
    suppssov1.a
    cA
    cV
    elex
    syl
    adantll
    adantr
    @13
    @10
    @15
    @10
    @3
    cZ
    wne
    @13
    @15
    @3
    cvv
    cZ
    eldifsni
    @13
    cA
    cY
    @3
    cZ
    @13
    @3
    cZ
    wceq
    cA
    cY
    wceq
    #
    cY
    cB
    cO
    co
    #
    cZ
    wceq
    #
    @13
    cB
    cR
    wcel
    #
    cY
    vv
    cv
    #
    cO
    co
    #
    cZ
    wceq
    #
    vv
    cR
    wral
    #
    @18
    wph
    @12
    @19
    @2
    suppssov1.b
    adantll
    @7
    @23
    @12
    wph
    @23
    @2
    wph
    @22
    vv
    cR
    suppssov1.o
    ralrimiva
    adantl
    adantr
    @22
    @18
    vv
    cB
    cR
    @20
    cB
    wceq
    @21
    @17
    cZ
    @20
    cB
    cY
    cO
    oveq2
    eqeq1d
    rspcva
    syl2anc
    @16
    @3
    @17
    cZ
    cA
    cY
    cB
    cO
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    syl5
    imp
    cA
    cvv
    cY
    eldifsn
    sylanbrc
    ex
    ss2rabdv
    @7
    vx
    cD
    @3
    @4
    cvv
    cvv
    cZ
    @4
    eqid
    @0
    @1
    wph
    simpll
    #
    @0
    @1
    wph
    simplr
    mptsuppdifd
    @7
    vx
    cD
    cA
    @8
    cvv
    cW
    cY
    @8
    eqid
    @24
    wph
    cY
    cW
    wcel
    @2
    suppssov1.y
    adantl
    mptsuppdifd
    3sstr4d
    wph
    @9
    cL
    wss
    @2
    suppssov1.s
    adantl
    sstrd
    ex
    @2
    wn
    #
    @6
    wph
    @25
    @5
    c0
    cL
    @2
    @4
    cvv
    wcel
    #
    @1
    wa
    @5
    c0
    wceq
    @0
    @26
    @1
    @0
    @26
    vx
    cD
    @3
    cvv
    mptexg
    @26
    cD
    @4
    cdm
    #
    cvv
    @3
    cvv
    wcel
    #
    vx
    cD
    wral
    @27
    cD
    wceq
    @28
    vx
    cD
    cA
    cB
    cO
    ovex
    rgenw
    vx
    cD
    @3
    cvv
    dmmptg
    ax-mp
    @4
    cvv
    dmexg
    syl5eqelr
    impbii
    anbi1i
    @4
    cZ
    supp0prc
    sylnbi
    cL
    0ss
    syl6eqss
    a1d
    pm2.61i
end
