include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "wne.mm"
include "simpr.mm"
include "colperpexlem3.mm"
include "simprl.mm"
include "ad5antr.mm"
include "simp-5r.mm"
include "orcd.mm"
include "tgbtwntriv1.mm"
include "eleq1.mm"
include "orbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "adantr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "tglowdim2ln.mm"
include "r19.29a.mm"
include "pm2.61dan.mm"

theorem colperpex
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vp: setvar p
  let vs: setvar s
  let vx: setvar x
  let vd: setvar d
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume colperpex.1: |- ( ph -> A e. P )
  assume colperpex.2: |- ( ph -> B e. P )
  assume colperpex.3: |- ( ph -> C e. P )
  assume colperpex.4: |- ( ph -> A =/= B )
  assume colperpex.5: |- ( ph -> G TarskiGDim>= 2 )

  disjoint .- p
  disjoint .- t
  disjoint p t
  disjoint A p
  disjoint A t
  disjoint B p
  disjoint B t
  disjoint C p
  disjoint C t
  disjoint G p
  disjoint G t
  disjoint I p
  disjoint I t
  disjoint L p
  disjoint L t
  disjoint P p
  disjoint P t
  disjoint p ph
  disjoint ph t
  disjoint .- s
  disjoint .- x
  disjoint p s
  disjoint p x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint A d
  disjoint A s
  disjoint A x
  disjoint d p
  disjoint d s
  disjoint d t
  disjoint d x
  disjoint B d
  disjoint B s
  disjoint B x
  disjoint C d
  disjoint C s
  disjoint C x
  disjoint G d
  disjoint G s
  disjoint G x
  disjoint I d
  disjoint I s
  disjoint I x
  disjoint L d
  disjoint L s
  disjoint L x
  disjoint P d
  disjoint P s
  disjoint P x
  disjoint d ph
  disjoint ph s
  disjoint ph x
  assert |- ( ph -> E. p e. P ( ( A L p ) ( perpG ` G ) ( A L B ) /\ E. t e. P ( ( t e. ( A L B ) \/ A = B ) /\ t e. ( C I p ) ) ) )

  proof
    wph
    cC
    cA
    cB
    cL
    co
    #
    wcel
    #
    cA
    vp
    cv
    #
    cL
    co
    @0
    cG
    cperpg
    cfv
    wbr
    #
    vt
    cv
    #
    @0
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    @4
    cC
    @2
    cI
    co
    #
    wcel
    #
    wa
    #
    vt
    cP
    wrex
    #
    wa
    #
    vp
    cP
    wrex
    #
    wph
    @1
    wa
    #
    vd
    cv
    #
    @0
    wcel
    wn
    #
    @13
    vd
    cP
    @14
    @15
    cP
    wcel
    #
    wa
    #
    @16
    wa
    #
    @3
    vs
    cv
    #
    @0
    wcel
    @6
    wo
    @20
    @15
    @2
    cI
    co
    wcel
    wa
    vs
    cP
    wrex
    #
    wa
    #
    vp
    cP
    wrex
    @13
    @19
    vs
    cA
    cB
    @15
    cP
    cG
    cI
    cL
    c.mi
    vp
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    cG
    cstrkg
    wcel
    #
    @1
    @17
    @16
    colperpex.g
    ad3antrrr
    wph
    cA
    cP
    wcel
    #
    @1
    @17
    @16
    colperpex.1
    ad3antrrr
    wph
    cB
    cP
    wcel
    #
    @1
    @17
    @16
    colperpex.2
    ad3antrrr
    @14
    @17
    @16
    simplr
    wph
    cA
    cB
    wne
    #
    @1
    @17
    @16
    colperpex.4
    ad3antrrr
    @18
    @16
    simpr
    colperpexlem3
    @19
    @22
    @12
    vp
    cP
    @19
    @2
    cP
    wcel
    #
    wa
    #
    @22
    @12
    @28
    @22
    wa
    #
    @3
    @11
    @28
    @3
    @21
    simprl
    @29
    cC
    cP
    wcel
    #
    @1
    @6
    wo
    #
    cC
    @8
    wcel
    #
    @11
    wph
    @30
    @1
    @17
    @16
    @27
    @22
    colperpex.3
    ad5antr
    #
    @29
    @1
    @6
    wph
    @1
    @17
    @16
    @27
    @22
    simp-5r
    orcd
    @29
    cC
    @2
    cP
    cG
    cI
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    wph
    @23
    @1
    @17
    @16
    @27
    @22
    colperpex.g
    ad5antr
    @33
    @19
    @27
    @22
    simplr
    tgbtwntriv1
    @10
    @31
    @32
    wa
    vt
    cC
    cP
    @4
    cC
    wceq
    #
    @7
    @31
    @9
    @32
    @34
    @5
    @1
    @6
    @4
    cC
    @0
    eleq1
    orbi1d
    @4
    cC
    @8
    eleq1
    anbi12d
    rspcev
    syl12anc
    jca
    ex
    reximdva
    mpd
    @14
    cA
    cB
    cP
    cG
    cI
    cL
    vd
    colperpex.p
    colperpex.i
    colperpex.l
    wph
    @23
    @1
    colperpex.g
    adantr
    wph
    cG
    c2
    cstrkgld
    wbr
    @1
    colperpex.5
    adantr
    wph
    @24
    @1
    colperpex.1
    adantr
    wph
    @25
    @1
    colperpex.2
    adantr
    wph
    @26
    @1
    colperpex.4
    adantr
    tglowdim2ln
    r19.29a
    wph
    @1
    wn
    #
    wa
    vt
    cA
    cB
    cC
    cP
    cG
    cI
    cL
    c.mi
    vp
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    wph
    @23
    @35
    colperpex.g
    adantr
    wph
    @24
    @35
    colperpex.1
    adantr
    wph
    @25
    @35
    colperpex.2
    adantr
    wph
    @30
    @35
    colperpex.3
    adantr
    wph
    @26
    @35
    colperpex.4
    adantr
    wph
    @35
    simpr
    colperpexlem3
    pm2.61dan
end
