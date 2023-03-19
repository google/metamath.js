include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wf1o.mm"
include "wiso.mm"
include "isof1o.mm"
include "syl.mm"
include "wfn.mm"
include "f1ofn.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "w3a.mm"
include "cfv.mm"
include "fnfvima.mm"
include "ne0i.mm"
include "3expia.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "wfo.mm"
include "f1ofo.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "syl5sseq.mm"
include "jctild.mm"
include "dffr3.mm"
include "cvv.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl5d.mm"
include "wfun.mm"
include "adantr.mm"
include "f1ofun.mm"
include "simpl.mm"
include "fvelima.mm"
include "syl2an.mm"
include "simpr.mm"
include "wb.mm"
include "ssel.mm"
include "imdistani.mm"
include "isomin.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "ineq2d.mm"
include "sylan9bb.mm"
include "syl5ibr.mm"
include "exp42.mm"
include "imp.mm"
include "com3l.mm"
include "com4t.mm"
include "reximdvai.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "ex.mm"
include "adantrd.mm"
include "a2d.mm"
include "syld.mm"
include "alrimdv.mm"
include "syl6ibr.mm"

theorem isofrlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume isofrlem.1: |- ( ph -> H Isom R , S ( A , B ) )
  assume isofrlem.2: |- ( ph -> ( H " x ) e. _V )

  disjoint A x
  disjoint B x
  disjoint H x
  disjoint ph x
  disjoint R x
  disjoint S x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint H w
  disjoint H y
  disjoint H z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R w
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( S Fr B -> R Fr A ) )

  proof
    wph
    cB
    cS
    wfr
    #
    vx
    cv
    #
    cA
    wss
    #
    @1
    c0
    wne
    #
    wa
    #
    @1
    cR
    ccnv
    vy
    cv
    #
    csn
    cima
    cin
    c0
    wceq
    #
    vy
    @1
    wrex
    #
    wi
    #
    vx
    wal
    cA
    cR
    wfr
    wph
    @0
    @8
    vx
    wph
    @0
    @4
    cH
    @1
    cima
    #
    cS
    ccnv
    #
    vw
    cv
    #
    csn
    #
    cima
    #
    cin
    #
    c0
    wceq
    #
    vw
    @9
    wrex
    #
    wi
    @8
    wph
    @4
    @9
    cB
    wss
    #
    @9
    c0
    wne
    #
    wa
    #
    @0
    @16
    wph
    cA
    cB
    cH
    wf1o
    #
    @4
    @19
    wi
    wph
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    @20
    isofrlem.1
    cA
    cB
    cR
    cS
    cH
    isof1o
    syl
    #
    @20
    @4
    @18
    @17
    @20
    cH
    cA
    wfn
    #
    @4
    @18
    wi
    cA
    cB
    cH
    f1ofn
    @23
    @2
    @3
    @18
    @3
    @5
    @1
    wcel
    #
    vy
    wex
    @23
    @2
    wa
    #
    @18
    vy
    @1
    n0
    @25
    @24
    @18
    vy
    @23
    @2
    @24
    @18
    @23
    @2
    @24
    w3a
    @5
    cH
    cfv
    #
    @9
    wcel
    @18
    cA
    @1
    cH
    @5
    fnfvima
    @9
    @26
    ne0i
    syl
    3expia
    exlimdv
    syl5bi
    expimpd
    syl
    @20
    cA
    cB
    cH
    wfo
    #
    @17
    cA
    cB
    cH
    f1ofo
    @27
    cH
    crn
    @9
    cB
    cH
    @1
    imassrn
    cA
    cB
    cH
    forn
    syl5sseq
    syl
    jctild
    syl
    @0
    vz
    cv
    #
    cB
    wss
    #
    @28
    c0
    wne
    #
    wa
    #
    @28
    @13
    cin
    #
    c0
    wceq
    #
    vw
    @28
    wrex
    #
    wi
    #
    vz
    wal
    #
    wph
    @19
    @16
    wi
    #
    vz
    vw
    cB
    cS
    dffr3
    wph
    @9
    cvv
    wcel
    @36
    @37
    wi
    isofrlem.2
    @35
    @37
    vz
    @9
    cvv
    @28
    @9
    wceq
    #
    @31
    @19
    @34
    @16
    @38
    @29
    @17
    @30
    @18
    @28
    @9
    cB
    sseq1
    @28
    @9
    c0
    neeq1
    anbi12d
    @33
    @15
    vw
    @28
    @9
    @38
    @32
    @14
    c0
    @28
    @9
    @13
    ineq1
    eqeq1d
    rexeqbi1dv
    imbi12d
    spcgv
    syl
    syl5bi
    syl5d
    wph
    @4
    @16
    @7
    wph
    @2
    @16
    @7
    wi
    #
    @3
    wph
    @2
    @39
    wph
    @2
    wa
    #
    @15
    @7
    vw
    @9
    @40
    @11
    @9
    wcel
    #
    @15
    wa
    #
    wa
    #
    @26
    @11
    wceq
    #
    vy
    @1
    wrex
    #
    @7
    @40
    cH
    wfun
    #
    @41
    @45
    @42
    @40
    @20
    @46
    wph
    @20
    @2
    @22
    adantr
    cA
    cB
    cH
    f1ofun
    syl
    @41
    @15
    simpl
    vy
    @11
    @1
    cH
    fvelima
    syl2an
    @43
    @44
    @6
    vy
    @1
    @40
    @42
    @24
    @44
    @6
    wi
    wi
    @24
    @44
    @40
    @42
    @6
    @40
    @24
    @44
    @42
    @6
    wi
    #
    wph
    @2
    @24
    @44
    @47
    wi
    wi
    wph
    @2
    @24
    @44
    @47
    @42
    @6
    wph
    @2
    @24
    wa
    #
    wa
    #
    @44
    wa
    @15
    @41
    @15
    simpr
    @49
    @6
    @9
    @10
    @26
    csn
    #
    cima
    #
    cin
    #
    c0
    wceq
    #
    @44
    @15
    wph
    @21
    @2
    @5
    cA
    wcel
    #
    wa
    @6
    @53
    wb
    @48
    isofrlem.1
    @2
    @24
    @54
    @1
    cA
    @5
    ssel
    imdistani
    cA
    cB
    @1
    @5
    cR
    cS
    cH
    isomin
    syl2an
    @44
    @52
    @14
    c0
    @44
    @51
    @13
    @9
    @44
    @50
    @12
    @10
    @26
    @11
    sneq
    imaeq2d
    ineq2d
    eqeq1d
    sylan9bb
    syl5ibr
    exp42
    imp
    com3l
    com4t
    imp
    reximdvai
    mpd
    rexlimdvaa
    ex
    adantrd
    a2d
    syld
    alrimdv
    vx
    vy
    cA
    cR
    dffr3
    syl6ibr
end
