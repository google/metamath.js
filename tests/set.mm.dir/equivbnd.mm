include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cbnd.mm"
include "isbnd3b.mm"
include "simprbi.mm"
include "syl.mm"
include "wa.mm"
include "cmul.mm"
include "rpred.mm"
include "remulcl.mm"
include "sylan.mm"
include "bndmet.mm"
include "adantr.mm"
include "metcl.mm"
include "3expb.mm"
include "simplr.mm"
include "crp.mm"
include "ad2antrr.mm"
include "lemul2d.mm"
include "adantlr.mm"
include "wi.mm"
include "remulcld.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "ralimdvva.mm"
include "wceq.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "sylanbrc.mm"

theorem equivbnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  assume equivbnd.1: |- ( ph -> M e. ( Bnd ` X ) )
  assume equivbnd.2: |- ( ph -> N e. ( Met ` X ) )
  assume equivbnd.3: |- ( ph -> R e. RR+ )
  assume equivbnd.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x N y ) <_ ( R x. ( x M y ) ) )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint R x
  disjoint R y
  disjoint r x
  disjoint r y
  disjoint M r
  disjoint r s
  disjoint N r
  disjoint s x
  disjoint s y
  disjoint N s
  disjoint ph r
  disjoint X r
  disjoint X s
  disjoint R s
  assert |- ( ph -> N e. ( Bnd ` X ) )

  proof
    wph
    cN
    cX
    cme
    cfv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cN
    co
    #
    vs
    cv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vs
    cr
    wrex
    #
    cN
    cX
    cbnd
    cfv
    #
    wcel
    equivbnd.2
    wph
    @2
    @3
    cM
    co
    #
    vr
    cv
    #
    cle
    wbr
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vr
    cr
    wrex
    #
    @8
    wph
    cM
    @9
    wcel
    #
    @14
    equivbnd.1
    @15
    cM
    @0
    wcel
    #
    @14
    vr
    vx
    vy
    cM
    cX
    isbnd3b
    simprbi
    syl
    wph
    @13
    @8
    vr
    cr
    wph
    @11
    cr
    wcel
    #
    wa
    #
    cR
    @11
    cmul
    co
    #
    cr
    wcel
    #
    @13
    @4
    @19
    cle
    wbr
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @8
    wph
    cR
    cr
    wcel
    #
    @17
    @20
    wph
    cR
    equivbnd.3
    rpred
    #
    cR
    @11
    remulcl
    sylan
    #
    @18
    @12
    @21
    vx
    vy
    cX
    cX
    @18
    @2
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    wa
    #
    wa
    #
    @12
    cR
    @10
    cmul
    co
    #
    @19
    cle
    wbr
    #
    @21
    @29
    @10
    @11
    cR
    @18
    @16
    @28
    @10
    cr
    wcel
    #
    wph
    @16
    @17
    wph
    @15
    @16
    equivbnd.1
    cM
    cX
    bndmet
    syl
    adantr
    @16
    @26
    @27
    @32
    @2
    @3
    cM
    cX
    metcl
    3expb
    sylan
    #
    wph
    @17
    @28
    simplr
    wph
    cR
    crp
    wcel
    @17
    @28
    equivbnd.3
    ad2antrr
    lemul2d
    @29
    @4
    @30
    cle
    wbr
    #
    @31
    @21
    wph
    @28
    @34
    @17
    equivbnd.4
    adantlr
    @29
    @4
    cr
    wcel
    #
    @30
    cr
    wcel
    @20
    @34
    @31
    wa
    @21
    wi
    @18
    @1
    @28
    @35
    wph
    @1
    @17
    equivbnd.2
    adantr
    @1
    @26
    @27
    @35
    @2
    @3
    cN
    cX
    metcl
    3expb
    sylan
    @29
    cR
    @10
    wph
    @23
    @17
    @28
    @24
    ad2antrr
    @33
    remulcld
    @18
    @20
    @28
    @25
    adantr
    @4
    @30
    @19
    letr
    syl3anc
    mpand
    sylbid
    ralimdvva
    @7
    @22
    vs
    @19
    cr
    @5
    @19
    wceq
    @6
    @21
    vx
    vy
    cX
    cX
    @5
    @19
    @4
    cle
    breq2
    2ralbidv
    rspcev
    syl6an
    rexlimdva
    mpd
    vs
    vx
    vy
    cN
    cX
    isbnd3b
    sylanbrc
end
