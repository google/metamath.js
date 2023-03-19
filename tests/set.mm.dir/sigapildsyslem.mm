include "ciun.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "iuneq1.mm"
include "0iun.mm"
include "syl6eq.mm"
include "difeq2d.mm"
include "dif0.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "ciin.mm"
include "iindif2.mm"
include "cfi.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cin.mm"
include "elin1d.mm"
include "ispisys.mm"
include "sylib.mm"
include "simprd.mm"
include "wral.mm"
include "cfn.mm"
include "nfv.mm"
include "nfan.mm"
include "simpld.mm"
include "elpwid.mm"
include "sseldd.mm"
include "difin2.mm"
include "syl.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "elin2d.mm"
include "isldsys.mm"
include "simp2d.mm"
include "adantlr.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpd.mm"
include "inelfi.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "simpr.mm"
include "cvv.mm"
include "vex.mm"
include "iinfi.mm"
include "mpan.mm"
include "eqeltrrd.mm"
include "pm2.61dane.mm"

theorem sigapildsyslem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let vn: setvar n
  let cL: class L
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vf: setvar f
  let vi: setvar i
  let vz: setvar z
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume sigapildsyslem.n: |- F/ n ph
  assume sigapildsyslem.1: |- ( ph -> t e. ( P i^i L ) )
  assume sigapildsyslem.2: |- ( ph -> A e. t )
  assume sigapildsyslem.3: |- ( ph -> N e. Fin )
  assume sigapildsyslem.4: |- ( ( ph /\ n e. N ) -> B e. t )

  disjoint A n
  disjoint B x
  disjoint N n
  disjoint N x
  disjoint n x
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint L n
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint O s
  disjoint O t
  disjoint O x
  disjoint P n
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint f i
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n z
  disjoint s z
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L f
  disjoint L i
  disjoint P f
  disjoint P i
  assert |- ( ph -> ( A \ U_ n e. N B ) e. t )

  proof
    wph
    cA
    vn
    cN
    cB
    ciun
    #
    cdif
    #
    vt
    cv
    #
    wcel
    cN
    c0
    wph
    cN
    c0
    wceq
    #
    wa
    @1
    cA
    @2
    @3
    @1
    cA
    wceq
    wph
    @3
    @1
    cA
    c0
    cdif
    cA
    @3
    @0
    c0
    cA
    @3
    @0
    vn
    c0
    cB
    ciun
    c0
    vn
    cN
    c0
    cB
    iuneq1
    vn
    cB
    0iun
    syl6eq
    difeq2d
    cA
    dif0
    syl6eq
    adantl
    wph
    cA
    @2
    wcel
    #
    @3
    sigapildsyslem.2
    adantr
    eqeltrd
    wph
    cN
    c0
    wne
    #
    wa
    #
    vn
    cN
    cA
    cB
    cdif
    #
    ciin
    #
    @1
    @2
    @5
    @8
    @1
    wceq
    wph
    vn
    cN
    cA
    cB
    iindif2
    adantl
    @6
    @2
    cfi
    cfv
    #
    @2
    @8
    @6
    @2
    cO
    cpw
    #
    cpw
    wcel
    #
    @9
    @2
    wss
    #
    @6
    @2
    cP
    wcel
    @11
    @12
    wa
    @6
    cP
    cL
    @2
    wph
    @2
    cP
    cL
    cin
    #
    wcel
    #
    @5
    sigapildsyslem.1
    adantr
    #
    elin1d
    cP
    @2
    cO
    vs
    dynkin.p
    ispisys
    sylib
    #
    simprd
    #
    @6
    @7
    @2
    wcel
    #
    vn
    cN
    wral
    #
    @5
    cN
    cfn
    wcel
    #
    @8
    @9
    wcel
    #
    @6
    @18
    vn
    cN
    wph
    @5
    vn
    sigapildsyslem.n
    @5
    vn
    nfv
    nfan
    @6
    vn
    cv
    cN
    wcel
    #
    @18
    @6
    @22
    wa
    #
    @7
    cO
    cB
    cdif
    #
    cA
    cin
    #
    @2
    @23
    cA
    cO
    wss
    #
    @7
    @25
    wceq
    @6
    @26
    @22
    @6
    cA
    cO
    @6
    @2
    @10
    cA
    @6
    @2
    @10
    @6
    @11
    @12
    @16
    simpld
    elpwid
    wph
    @4
    @5
    sigapildsyslem.2
    adantr
    #
    sseldd
    elpwid
    adantr
    cA
    cB
    cO
    difin2
    syl
    @23
    @9
    @2
    @25
    @6
    @12
    @22
    @17
    adantr
    @23
    @14
    @24
    @2
    wcel
    #
    @4
    @25
    @9
    wcel
    @6
    @14
    @22
    @15
    adantr
    @23
    cO
    vx
    cv
    #
    cdif
    #
    @2
    wcel
    #
    vx
    @2
    wral
    #
    @28
    @6
    @32
    @22
    @6
    c0
    @2
    wcel
    #
    @32
    @29
    com
    cdom
    wbr
    vy
    @29
    vy
    cv
    wdisj
    wa
    @29
    cuni
    @2
    wcel
    wi
    vx
    @2
    cpw
    wral
    #
    @6
    @11
    @33
    @32
    @34
    w3a
    #
    @6
    @2
    cL
    wcel
    @11
    @35
    wa
    @6
    cP
    cL
    @2
    @15
    elin2d
    vx
    vy
    @2
    cL
    cO
    vs
    dynkin.l
    isldsys
    sylib
    simprd
    simp2d
    adantr
    @23
    cB
    @2
    wcel
    #
    @32
    @28
    wi
    wph
    @22
    @36
    @5
    sigapildsyslem.4
    adantlr
    @31
    @28
    vx
    cB
    @2
    @28
    vx
    nfv
    @29
    cB
    wceq
    @30
    @24
    @2
    @29
    cB
    cO
    difeq2
    eleq1d
    rspc
    syl
    mpd
    @6
    @4
    @22
    @27
    adantr
    @24
    cA
    @13
    @2
    inelfi
    syl3anc
    sseldd
    eqeltrd
    ex
    ralrimi
    wph
    @5
    simpr
    wph
    @20
    @5
    sigapildsyslem.3
    adantr
    @2
    cvv
    wcel
    @19
    @5
    @20
    w3a
    @21
    vt
    vex
    vn
    cN
    @7
    @2
    cvv
    iinfi
    mpan
    syl3anc
    sseldd
    eqeltrrd
    pm2.61dane
end
