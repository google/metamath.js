include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wbr.mm"
include "csn.mm"
include "eldifad.mm"
include "wf1o.mm"
include "wf.mm"
include "wf1.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "ad2antrr.mm"
include "wo.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "cdomn.mm"
include "wb.mm"
include "adantr.mm"
include "simpr.mm"
include "domneq0.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "biimpa.mm"
include "ord.mm"
include "necon1ad.mm"
include "mpd.mm"
include "ex.mm"
include "ralrimiva.mm"
include "cghm.mm"
include "cmpt.mm"
include "crg.mm"
include "domnring.mm"
include "ringrghm.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "ghmf1.mm"
include "mpbird.mm"
include "cen.mm"
include "cfn.mm"
include "enrefg.mm"
include "f1finf1o.mm"
include "mpbid.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ringidcl.mm"
include "ffvelrnd.mm"
include "dvdsrmul.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "f1ocnvfv2.mm"
include "eqtr3d.mm"
include "breqtrd.mm"

theorem fidomndrnglem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let c.0: class .0.
  let vy: setvar y
  assume fidomndrng.b: |- B = ( Base ` R )
  assume fidomndrng.z: |- .0. = ( 0g ` R )
  assume fidomndrng.o: |- .1. = ( 1r ` R )
  assume fidomndrng.d: |- .|| = ( ||r ` R )
  assume fidomndrng.t: |- .x. = ( .r ` R )
  assume fidomndrng.r: |- ( ph -> R e. Domn )
  assume fidomndrng.x: |- ( ph -> B e. Fin )
  assume fidomndrng.a: |- ( ph -> A e. ( B \ { .0. } ) )
  assume fidomndrng.f: |- F = ( x e. B |-> ( x .x. A ) )

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint .x. x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint ph y
  disjoint R y
  disjoint .x. y
  disjoint .1. y
  disjoint .0. y
  assert |- ( ph -> A .|| .1. )

  proof
    wph
    cA
    c.1
    cF
    ccnv
    #
    cfv
    #
    cA
    c.x
    co
    #
    c.1
    c.pa
    wph
    cA
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    cA
    @2
    c.pa
    wbr
    wph
    cA
    cB
    c.0
    csn
    #
    fidomndrng.a
    eldifad
    #
    wph
    cB
    cB
    c.1
    @0
    wph
    cB
    cB
    cF
    wf1o
    #
    cB
    cB
    @0
    wf1o
    cB
    cB
    @0
    wf
    wph
    cB
    cB
    cF
    wf1
    #
    @7
    wph
    @8
    vy
    cv
    #
    cF
    cfv
    #
    c.0
    wceq
    #
    @9
    c.0
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    wph
    @13
    vy
    cB
    wph
    @9
    cB
    wcel
    #
    wa
    #
    @11
    @12
    @16
    @11
    wa
    #
    cA
    c.0
    wne
    #
    @12
    wph
    @18
    @15
    @11
    wph
    cA
    cB
    @5
    cdif
    wcel
    @18
    fidomndrng.a
    cA
    cB
    c.0
    eldifsni
    syl
    ad2antrr
    @17
    @12
    cA
    c.0
    @17
    @12
    cA
    c.0
    wceq
    #
    @16
    @11
    @12
    @19
    wo
    #
    @16
    @11
    @9
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @20
    @16
    @10
    @21
    c.0
    @15
    @10
    @21
    wceq
    wph
    vx
    @9
    vx
    cv
    #
    cA
    c.x
    co
    #
    @21
    cB
    cF
    @23
    @9
    cA
    c.x
    oveq1
    #
    fidomndrng.f
    @9
    cA
    c.x
    ovex
    fvmpt
    adantl
    eqeq1d
    @16
    cR
    cdomn
    wcel
    #
    @15
    @3
    @22
    @20
    wb
    wph
    @26
    @15
    fidomndrng.r
    adantr
    wph
    @15
    simpr
    wph
    @3
    @15
    @6
    adantr
    cB
    cR
    c.x
    @9
    cA
    c.0
    fidomndrng.b
    fidomndrng.t
    fidomndrng.z
    domneq0
    syl3anc
    bitrd
    biimpa
    ord
    necon1ad
    mpd
    ex
    ralrimiva
    wph
    cF
    cR
    cR
    cghm
    co
    #
    wcel
    @8
    @14
    wb
    wph
    cF
    vx
    cB
    @24
    cmpt
    #
    @27
    fidomndrng.f
    wph
    cR
    crg
    wcel
    #
    @3
    @28
    @27
    wcel
    wph
    @26
    @29
    fidomndrng.r
    cR
    domnring
    syl
    #
    @6
    vx
    cB
    cR
    c.x
    cA
    fidomndrng.b
    fidomndrng.t
    ringrghm
    syl2anc
    syl5eqel
    vy
    cR
    cR
    c.0
    cF
    cB
    cB
    c.0
    fidomndrng.b
    fidomndrng.b
    fidomndrng.z
    fidomndrng.z
    ghmf1
    syl
    mpbird
    wph
    cB
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    @8
    @7
    wb
    wph
    @32
    @31
    fidomndrng.x
    cB
    cfn
    enrefg
    syl
    fidomndrng.x
    cB
    cB
    cF
    f1finf1o
    syl2anc
    mpbid
    #
    cB
    cB
    cF
    f1ocnv
    cB
    cB
    @0
    f1of
    3syl
    wph
    @29
    c.1
    cB
    wcel
    #
    @30
    cB
    cR
    c.1
    fidomndrng.b
    fidomndrng.o
    ringidcl
    syl
    #
    ffvelrnd
    #
    cB
    c.pa
    cR
    c.x
    cA
    @1
    fidomndrng.b
    fidomndrng.d
    fidomndrng.t
    dvdsrmul
    syl2anc
    wph
    @1
    cF
    cfv
    #
    @2
    c.1
    wph
    @4
    @37
    @2
    wceq
    @36
    vy
    @1
    @21
    @2
    cB
    cF
    @9
    @1
    cA
    c.x
    oveq1
    cF
    @28
    vy
    cB
    @21
    cmpt
    fidomndrng.f
    vx
    vy
    cB
    @24
    @21
    @25
    cbvmptv
    eqtri
    @1
    cA
    c.x
    ovex
    fvmpt
    syl
    wph
    @7
    @34
    @37
    c.1
    wceq
    @33
    @35
    cB
    cB
    c.1
    cF
    f1ocnvfv2
    syl2anc
    eqtr3d
    breqtrd
end
