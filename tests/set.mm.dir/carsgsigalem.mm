include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "unidm.mm"
include "simpr.mm"
include "uneq2d.mm"
include "syl5reqr.mm"
include "fveq2d.mm"
include "cxr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wf.mm"
include "simp1.mm"
include "syl.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "simp3.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "xraddge02.mm"
include "imp.mm"
include "syl21anc.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "cpr.mm"
include "cesum.mm"
include "cuni.mm"
include "uniprg.mm"
include "3adant1.mm"
include "com.mm"
include "cdom.mm"
include "wss.mm"
include "prct.mm"
include "prssi.mm"
include "cvv.mm"
include "wi.mm"
include "prex.mm"
include "breq1.mm"
include "sseq1.mm"
include "3anbi23d.mm"
include "unieq.mm"
include "esumeq1.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "syl3anc.mm"
include "eqbrtrrd.mm"
include "adantlr.mm"
include "esumpr.mm"
include "breqtrd.mm"
include "pm2.61dane.mm"

theorem carsgsigalem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  let vf: setvar f
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let vm: setvar m
  let cA: class A
  let vb: setvar b
  let cE: class E
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )

  disjoint M e
  disjoint O e
  disjoint e ph
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint M f
  disjoint M x
  disjoint M y
  disjoint O f
  disjoint O x
  disjoint O y
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O m
  disjoint a ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint E x
  disjoint E y
  disjoint M b
  disjoint b ph
  assert |- ( ( ph /\ e e. ~P O /\ f e. ~P O ) -> ( M ` ( e u. f ) ) <_ ( ( M ` e ) +e ( M ` f ) ) )

  proof
    wph
    ve
    cv
    #
    cO
    cpw
    #
    wcel
    #
    vf
    cv
    #
    @1
    wcel
    #
    w3a
    #
    @0
    @3
    cun
    #
    cM
    cfv
    #
    @0
    cM
    cfv
    #
    @3
    cM
    cfv
    #
    cxad
    co
    #
    cle
    wbr
    @0
    @3
    @5
    @0
    @3
    wceq
    #
    wa
    #
    @7
    @8
    @10
    cle
    @12
    @6
    @0
    cM
    @12
    @0
    @0
    @0
    cun
    @6
    @0
    unidm
    @12
    @0
    @3
    @0
    @5
    @11
    simpr
    #
    uneq2d
    syl5reqr
    fveq2d
    @12
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    @8
    @10
    cle
    wbr
    #
    @5
    @14
    @11
    @5
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @8
    cc0
    cpnf
    iccssxr
    @5
    @1
    @18
    @0
    cM
    @5
    wph
    @1
    @18
    cM
    wf
    wph
    @2
    @4
    simp1
    #
    carsgval.2
    syl
    #
    wph
    @2
    @4
    simp2
    #
    ffvelrnd
    #
    sseldi
    adantr
    #
    @12
    @8
    @9
    cxr
    @12
    @0
    @3
    cM
    @13
    fveq2d
    @23
    eqeltrrd
    @12
    @9
    @18
    wcel
    #
    @16
    @5
    @24
    @11
    @5
    @1
    @18
    @3
    cM
    @20
    wph
    @2
    @4
    simp3
    #
    ffvelrnd
    #
    adantr
    @24
    @15
    @16
    @9
    elxrge0
    simprbi
    syl
    @14
    @15
    wa
    @16
    @17
    @8
    @9
    xraddge02
    imp
    syl21anc
    eqbrtrd
    @5
    @0
    @3
    wne
    #
    wa
    #
    @7
    @0
    @3
    cpr
    #
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    #
    @10
    cle
    @5
    @7
    @32
    cle
    wbr
    @27
    @5
    @29
    cuni
    #
    cM
    cfv
    #
    @7
    @32
    cle
    @2
    @4
    @34
    @7
    wceq
    wph
    @2
    @4
    wa
    @33
    @6
    cM
    @0
    @3
    @1
    @1
    uniprg
    fveq2d
    3adant1
    @5
    wph
    @29
    com
    cdom
    wbr
    #
    @29
    @1
    wss
    #
    @34
    @32
    cle
    wbr
    #
    @19
    @2
    @4
    @35
    wph
    @0
    @3
    @1
    @1
    prct
    3adant1
    @2
    @4
    @36
    wph
    @0
    @3
    @1
    prssi
    3adant1
    @29
    cvv
    wcel
    wph
    @35
    @36
    w3a
    #
    @37
    wi
    #
    @0
    @3
    prex
    wph
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @40
    @1
    wss
    #
    w3a
    #
    @40
    cuni
    #
    cM
    cfv
    #
    @40
    @31
    vy
    cesum
    #
    cle
    wbr
    #
    wi
    @39
    vx
    @29
    cvv
    @40
    @29
    wceq
    #
    @43
    @38
    @47
    @37
    @48
    @41
    @35
    @42
    @36
    wph
    @40
    @29
    com
    cdom
    breq1
    @40
    @29
    @1
    sseq1
    3anbi23d
    @48
    @45
    @34
    @46
    @32
    cle
    @48
    @44
    @33
    cM
    @40
    @29
    unieq
    fveq2d
    @40
    @29
    @31
    vy
    esumeq1
    breq12d
    imbi12d
    carsgsiga.2
    vtoclg
    ax-mp
    syl3anc
    eqbrtrrd
    adantr
    @28
    @0
    @3
    @31
    @8
    vy
    @9
    @1
    @1
    @5
    @30
    @0
    wceq
    #
    @31
    @8
    wceq
    @27
    @5
    @49
    wa
    @30
    @0
    cM
    @5
    @49
    simpr
    fveq2d
    adantlr
    @5
    @30
    @3
    wceq
    #
    @31
    @9
    wceq
    @27
    @5
    @50
    wa
    @30
    @3
    cM
    @5
    @50
    simpr
    fveq2d
    adantlr
    @5
    @2
    @27
    @21
    adantr
    @5
    @4
    @27
    @25
    adantr
    @5
    @8
    @18
    wcel
    @27
    @22
    adantr
    @5
    @24
    @27
    @26
    adantr
    @5
    @27
    simpr
    esumpr
    breqtrd
    pm2.61dane
end
