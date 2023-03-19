include "crg.mm"
include "wcel.mm"
include "cec.mm"
include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "cqs.mm"
include "cvv.mm"
include "eqid.mm"
include "wer.mm"
include "cbs.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "erex.mm"
include "sylc.mm"
include "qusval.mm"
include "quslem.mm"
include "co.mm"
include "adantr.mm"
include "simprl.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "ercpbl.mm"
include "ringcl.mm"
include "imasring.mm"
include "divsfval.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "anbi2d.mm"
include "mpbird.mm"

theorem qusring2
  let wph: wff ph
  let c.pl: class .+
  let c.sm: class .~
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cV: class V
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume qusring2.u: |- ( ph -> U = ( R /s .~ ) )
  assume qusring2.v: |- ( ph -> V = ( Base ` R ) )
  assume qusring2.p: |- .+ = ( +g ` R )
  assume qusring2.t: |- .x. = ( .r ` R )
  assume qusring2.o: |- .1. = ( 1r ` R )
  assume qusring2.r: |- ( ph -> .~ Er V )
  assume qusring2.e1: |- ( ph -> ( ( a .~ p /\ b .~ q ) -> ( a .+ b ) .~ ( p .+ q ) ) )
  assume qusring2.e2: |- ( ph -> ( ( a .~ p /\ b .~ q ) -> ( a .x. b ) .~ ( p .x. q ) ) )
  assume qusring2.x: |- ( ph -> R e. Ring )

  disjoint p q
  disjoint .+ p
  disjoint .+ q
  disjoint .1. p
  disjoint .1. q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint U a
  disjoint b p
  disjoint b q
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .~ a
  disjoint .~ b
  disjoint .~ p
  disjoint .~ q
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint .x. p
  disjoint .x. q
  disjoint R p
  disjoint R q
  disjoint p u
  disjoint p x
  disjoint p y
  disjoint q u
  disjoint q x
  disjoint q y
  disjoint u x
  disjoint u y
  disjoint .+ u
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint .1. u
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint V u
  disjoint V x
  disjoint V y
  disjoint .~ u
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint .x. u
  disjoint .x. x
  disjoint .x. y
  disjoint R u
  assert |- ( ph -> ( U e. Ring /\ [ .1. ] .~ = ( 1r ` U ) ) )

  proof
    wph
    cU
    crg
    wcel
    #
    c.1
    c.sm
    cec
    #
    cU
    cur
    cfv
    #
    wceq
    #
    wa
    @0
    c.1
    vu
    cV
    vu
    cv
    c.sm
    cec
    cmpt
    #
    cfv
    #
    @2
    wceq
    #
    wa
    wph
    cV
    c.sm
    cqs
    c.pl
    cR
    c.x
    cU
    c.1
    @4
    cV
    vq
    vp
    va
    vb
    wph
    vu
    c.sm
    cR
    cU
    @4
    cV
    cvv
    crg
    qusring2.u
    qusring2.v
    @4
    eqid
    #
    wph
    cV
    c.sm
    wer
    cV
    cvv
    wcel
    c.sm
    cvv
    wcel
    qusring2.r
    wph
    cV
    cR
    cbs
    cfv
    #
    cvv
    qusring2.v
    cR
    cbs
    fvex
    syl6eqel
    #
    cV
    c.sm
    cvv
    erex
    sylc
    #
    qusring2.x
    qusval
    qusring2.v
    qusring2.p
    qusring2.t
    qusring2.o
    wph
    vu
    c.sm
    cR
    cU
    @4
    cV
    cvv
    crg
    qusring2.u
    qusring2.v
    @7
    @10
    qusring2.x
    quslem
    wph
    vu
    va
    cv
    #
    vb
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    c.pl
    c.sm
    @4
    cV
    vx
    vy
    qusring2.r
    @9
    @7
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    wa
    #
    wa
    #
    @15
    @17
    c.pl
    co
    #
    @8
    cV
    @20
    cR
    crg
    wcel
    #
    @15
    @8
    wcel
    #
    @17
    @8
    wcel
    #
    @21
    @8
    wcel
    wph
    @22
    @19
    qusring2.x
    adantr
    #
    @20
    @15
    cV
    @8
    wph
    @16
    @18
    simprl
    wph
    cV
    @8
    wceq
    @19
    qusring2.v
    adantr
    #
    eleqtrd
    #
    @20
    @17
    cV
    @8
    wph
    @16
    @18
    simprr
    @26
    eleqtrd
    #
    @8
    c.pl
    cR
    @15
    @17
    @8
    eqid
    #
    qusring2.p
    ringacl
    syl3anc
    @26
    eleqtrrd
    qusring2.e1
    ercpbl
    wph
    vu
    @11
    @12
    @13
    @14
    c.x
    c.sm
    @4
    cV
    vx
    vy
    qusring2.r
    @9
    @7
    @20
    @15
    @17
    c.x
    co
    #
    @8
    cV
    @20
    @22
    @23
    @24
    @30
    @8
    wcel
    @25
    @27
    @28
    @8
    cR
    c.x
    @15
    @17
    @29
    qusring2.t
    ringcl
    syl3anc
    @26
    eleqtrrd
    qusring2.e2
    ercpbl
    qusring2.x
    imasring
    wph
    @3
    @6
    @0
    wph
    @1
    @5
    @2
    wph
    @5
    @1
    wph
    vu
    c.1
    c.sm
    @4
    cV
    qusring2.r
    @9
    @7
    divsfval
    eqcomd
    eqeq1d
    anbi2d
    mpbird
end
