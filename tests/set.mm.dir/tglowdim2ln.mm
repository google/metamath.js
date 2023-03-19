include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wceq.mm"
include "wo.mm"
include "tglowdim2l.mm"
include "adantr.mm"
include "wa.mm"
include "w3a.mm"
include "simplr3.mm"
include "simpllr.mm"
include "eleq1.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "neqned.mm"
include "wne.mm"
include "tgelrnln.mm"
include "tglinethru.mm"
include "eleqtrd.mm"
include "ex.mm"
include "orrd.mm"
include "orcomd.mm"
include "ralrimivvva.mm"
include "dfral2.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "sylib.mm"
include "pm2.65da.mm"
include "rexnal.mm"
include "sylibr.mm"

theorem tglowdim2ln
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglowdim2l.1: |- ( ph -> G TarskiGDim>= 2 )
  assume tglowdim2ln.a: |- ( ph -> A e. P )
  assume tglowdim2ln.b: |- ( ph -> B e. P )
  assume tglowdim2ln.1: |- ( ph -> A =/= B )

  disjoint G c
  disjoint I c
  disjoint P c
  disjoint c ph
  disjoint A c
  disjoint B c
  disjoint L c
  disjoint a b
  disjoint a c
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b z
  disjoint G b
  disjoint c z
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I z
  disjoint P a
  disjoint P b
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint ph z
  disjoint A a
  disjoint A b
  disjoint A z
  disjoint B a
  disjoint B b
  disjoint B z
  disjoint L a
  disjoint L b
  disjoint L z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> E. c e. P -. c e. ( A L B ) )

  proof
    wph
    vc
    cv
    #
    cA
    cB
    cL
    co
    #
    wcel
    #
    vc
    cP
    wral
    #
    wn
    @2
    wn
    vc
    cP
    wrex
    wph
    @3
    vz
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cL
    co
    #
    wcel
    #
    @5
    @6
    wceq
    #
    wo
    #
    wn
    vz
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    wph
    @13
    @3
    wph
    cP
    cG
    cI
    cL
    va
    vb
    vz
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglowdim2l.1
    tglowdim2l
    adantr
    wph
    @3
    wa
    #
    @10
    vz
    cP
    wral
    #
    vb
    cP
    wral
    #
    va
    cP
    wral
    #
    @13
    wn
    #
    @14
    @10
    va
    vb
    vz
    cP
    cP
    cP
    @14
    @5
    cP
    wcel
    #
    @6
    cP
    wcel
    #
    @4
    cP
    wcel
    #
    w3a
    #
    wa
    #
    @9
    @8
    @23
    @9
    @8
    @23
    @9
    wn
    #
    @8
    @23
    @24
    wa
    #
    @4
    @1
    @7
    @25
    @21
    @3
    @4
    @1
    wcel
    #
    @19
    @20
    @21
    @14
    @24
    simplr3
    wph
    @3
    @22
    @24
    simpllr
    #
    @2
    @26
    vc
    @4
    cP
    @0
    @4
    @1
    eleq1
    rspcva
    syl2anc
    @25
    @1
    cP
    @5
    @6
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    cG
    cstrkg
    wcel
    @3
    @22
    @24
    tglineintmo.g
    ad3antrrr
    #
    @19
    @20
    @21
    @14
    @24
    simplr1
    #
    @19
    @20
    @21
    @14
    @24
    simplr2
    #
    @25
    @5
    @6
    @23
    @24
    simpr
    neqned
    #
    @31
    @25
    cP
    cG
    cI
    cL
    cA
    cB
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @28
    wph
    cA
    cP
    wcel
    @3
    @22
    @24
    tglowdim2ln.a
    ad3antrrr
    wph
    cB
    cP
    wcel
    @3
    @22
    @24
    tglowdim2ln.b
    ad3antrrr
    wph
    cA
    cB
    wne
    @3
    @22
    @24
    tglowdim2ln.1
    ad3antrrr
    tgelrnln
    @25
    @19
    @3
    @5
    @1
    wcel
    #
    @29
    @27
    @2
    @32
    vc
    @5
    cP
    @0
    @5
    @1
    eleq1
    rspcva
    syl2anc
    @25
    @20
    @3
    @6
    @1
    wcel
    #
    @30
    @27
    @2
    @33
    vc
    @6
    cP
    @0
    @6
    @1
    eleq1
    rspcva
    syl2anc
    tglinethru
    eleqtrd
    ex
    orrd
    orcomd
    ralrimivvva
    @17
    @12
    wn
    #
    va
    cP
    wral
    @18
    @16
    @34
    va
    cP
    @16
    @11
    wn
    #
    vb
    cP
    wral
    @34
    @15
    @35
    vb
    cP
    @10
    vz
    cP
    dfral2
    ralbii
    @11
    vb
    cP
    ralnex
    bitri
    ralbii
    @12
    va
    cP
    ralnex
    bitri
    sylib
    pm2.65da
    @2
    vc
    cP
    rexnal
    sylibr
end
