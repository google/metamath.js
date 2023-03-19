include "cfv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "incom.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "cdif.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "cvv.mm"
include "fvex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleqtrd.mm"
include "eldifn.mm"
include "wss.mm"
include "cuz.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "3jca.mm"
include "elfzo2.mm"
include "sylibr.mm"
include "ssiun2s.mm"
include "ssneld.mm"
include "sylc.mm"
include "eldifi.mm"
include "con3i.mm"
include "adantr.mm"
include "eqcomd.mm"
include "neleqtrd.mm"
include "ralrimiva.mm"
include "disj.mm"
include "eqtrd.mm"

theorem iundjiunlem
  let wph: wff ph
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume iundjiunlem.z: |- Z = ( ZZ>= ` N )
  assume iundjiunlem.f: |- F = ( n e. Z |-> ( ( E ` n ) \ U_ i e. ( N ..^ n ) ( E ` i ) ) )
  assume iundjiunlem.j: |- ( ph -> J e. Z )
  assume iundjiunlem.k: |- ( ph -> K e. Z )
  assume iundjiunlem.lt: |- ( ph -> J < K )

  disjoint E i
  disjoint E n
  disjoint i n
  disjoint J i
  disjoint J n
  disjoint K i
  disjoint K n
  disjoint N i
  disjoint N n
  disjoint Z n
  disjoint F x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( F ` J ) i^i ( F ` K ) ) = (/) )

  proof
    wph
    cJ
    cF
    cfv
    #
    cK
    cF
    cfv
    #
    cin
    #
    @1
    @0
    cin
    #
    c0
    @2
    @3
    wceq
    wph
    @0
    @1
    incom
    a1i
    wph
    vx
    cv
    #
    @0
    wcel
    wn
    #
    vx
    @1
    wral
    @3
    c0
    wceq
    wph
    @5
    vx
    @1
    wph
    @4
    @1
    wcel
    #
    wa
    #
    cJ
    cE
    cfv
    #
    vi
    cN
    cJ
    cfzo
    co
    #
    vi
    cv
    #
    cE
    cfv
    #
    ciun
    #
    cdif
    #
    @0
    @4
    @7
    @4
    @8
    wcel
    #
    wn
    #
    @4
    @13
    wcel
    #
    wn
    @7
    wph
    @4
    vi
    cN
    cK
    cfzo
    co
    #
    @11
    ciun
    #
    wcel
    wn
    #
    @15
    wph
    @6
    simpl
    #
    @7
    @4
    cK
    cE
    cfv
    #
    @18
    cdif
    #
    wcel
    @19
    @7
    @4
    @1
    @22
    wph
    @6
    simpr
    @7
    wph
    @1
    @22
    wceq
    #
    @20
    wph
    cK
    cZ
    wcel
    @23
    iundjiunlem.k
    vn
    cK
    vn
    cv
    #
    cE
    cfv
    #
    vi
    cN
    @24
    cfzo
    co
    #
    @11
    ciun
    #
    cdif
    #
    @22
    cZ
    cF
    @24
    cK
    wceq
    #
    @25
    @21
    @27
    @18
    @24
    cK
    cE
    fveq2
    @29
    vi
    @26
    @17
    @11
    @24
    cK
    cN
    cfzo
    oveq2
    iuneq1d
    difeq12d
    iundjiunlem.f
    @21
    cvv
    wcel
    @22
    cvv
    wcel
    cK
    cE
    fvex
    @21
    @18
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    syl
    eleqtrd
    @4
    @21
    @18
    eldifn
    syl
    wph
    @8
    @18
    @4
    wph
    cJ
    @17
    wcel
    #
    @8
    @18
    wss
    wph
    cJ
    cN
    cuz
    cfv
    #
    wcel
    #
    cK
    cz
    wcel
    #
    cJ
    cK
    clt
    wbr
    #
    w3a
    @30
    wph
    @32
    @33
    @34
    wph
    cJ
    cZ
    @31
    iundjiunlem.j
    iundjiunlem.z
    syl6eleq
    wph
    cK
    @31
    wcel
    @33
    wph
    cK
    cZ
    @31
    iundjiunlem.k
    cZ
    @31
    wceq
    wph
    iundjiunlem.z
    a1i
    eleqtrd
    cN
    cK
    eluzelz
    syl
    iundjiunlem.lt
    3jca
    cJ
    cN
    cK
    elfzo2
    sylibr
    vi
    @17
    @11
    cJ
    @8
    @10
    cJ
    cE
    fveq2
    ssiun2s
    syl
    ssneld
    sylc
    @16
    @14
    @4
    @8
    @12
    eldifi
    con3i
    syl
    @7
    @0
    @13
    wph
    @0
    @13
    wceq
    #
    @6
    wph
    cJ
    cZ
    wcel
    @35
    iundjiunlem.j
    vn
    cJ
    @28
    @13
    cZ
    cF
    @24
    cJ
    wceq
    #
    @25
    @8
    @27
    @12
    @24
    cJ
    cE
    fveq2
    @36
    vi
    @26
    @9
    @11
    @24
    cJ
    cN
    cfzo
    oveq2
    iuneq1d
    difeq12d
    iundjiunlem.f
    @8
    cvv
    wcel
    @13
    cvv
    wcel
    cJ
    cE
    fvex
    @8
    @12
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    adantr
    eqcomd
    neleqtrd
    ralrimiva
    vx
    @1
    @0
    disj
    sylibr
    eqtrd
end
