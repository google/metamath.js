include "cv.mm"
include "wne.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "chpg.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "simprl.mm"
include "tglnpt.mm"
include "ad3antrrr.mm"
include "simprrl.mm"
include "perpln1.mm"
include "tglnne.mm"
include "necomd.mm"
include "tgelrnln.mm"
include "crn.mm"
include "tglinecom.mm"
include "eqbrtrd.mm"
include "perpcom.mm"
include "simpr.mm"
include "simplr.mm"
include "simprrr.mm"
include "oppcom.mm"
include "lnopp2hpgb.mm"
include "mpbid.mm"
include "jca.mm"
include "chlg.mm"
include "eqid.mm"
include "oppne2.mm"
include "c2.mm"
include "cstrkgld.mm"
include "oppperpex.mm"
include "reximddv.mm"
include "hpgerlem.mm"
include "r19.29a.mm"
include "tglnpt2.mm"

theorem lnperpex
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume lmiopp.p: |- P = ( Base ` G )
  assume lmiopp.m: |- .- = ( dist ` G )
  assume lmiopp.i: |- I = ( Itv ` G )
  assume lmiopp.l: |- L = ( LineG ` G )
  assume lmiopp.g: |- ( ph -> G e. TarskiG )
  assume lmiopp.h: |- ( ph -> G TarskiGDim>= 2 )
  assume lmiopp.d: |- ( ph -> D e. ran L )
  assume lmiopp.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume lnperpex.a: |- ( ph -> A e. D )
  assume lnperpex.q: |- ( ph -> Q e. P )
  assume lnperpex.1: |- ( ph -> -. Q e. D )

  disjoint .- a
  disjoint .- b
  disjoint .- p
  disjoint .- t
  disjoint a b
  disjoint a p
  disjoint a t
  disjoint b p
  disjoint b t
  disjoint p t
  disjoint A a
  disjoint A b
  disjoint A p
  disjoint A t
  disjoint D a
  disjoint D b
  disjoint D p
  disjoint D t
  disjoint G a
  disjoint G b
  disjoint G p
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I p
  disjoint I t
  disjoint L a
  disjoint L b
  disjoint L p
  disjoint L t
  disjoint O a
  disjoint O b
  disjoint O p
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P p
  disjoint P t
  disjoint Q a
  disjoint Q b
  disjoint Q p
  disjoint Q t
  disjoint a ph
  disjoint b ph
  disjoint p ph
  disjoint ph t
  disjoint A c
  disjoint A d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c p
  disjoint c t
  disjoint d p
  disjoint d t
  disjoint D c
  disjoint D d
  disjoint G c
  disjoint G d
  disjoint I c
  disjoint L c
  disjoint L d
  disjoint P c
  disjoint P d
  disjoint Q c
  disjoint Q d
  disjoint c ph
  disjoint d ph
  assert |- ( ph -> E. p e. P ( D ( perpG ` G ) ( p L A ) /\ p ( ( hpG ` G ) ` D ) Q ) )

  proof
    wph
    cA
    vd
    cv
    #
    wne
    #
    cD
    vp
    cv
    #
    cA
    cL
    co
    #
    cG
    cperpg
    cfv
    #
    wbr
    #
    @2
    cQ
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    #
    wa
    #
    vp
    cP
    wrex
    #
    vd
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    @1
    wa
    #
    cQ
    vc
    cv
    #
    cO
    wbr
    #
    @8
    vc
    cP
    @10
    @11
    cP
    wcel
    #
    wa
    #
    @12
    wa
    #
    cA
    @2
    cL
    co
    #
    cD
    @4
    wbr
    #
    @11
    @2
    cO
    wbr
    #
    wa
    #
    @7
    vp
    cP
    @15
    @2
    cP
    wcel
    #
    @19
    wa
    #
    wa
    #
    @5
    @6
    @22
    @3
    cD
    cP
    cG
    cI
    cL
    c.mi
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.l
    @15
    cG
    cstrkg
    wcel
    #
    @21
    @10
    @23
    @13
    @12
    wph
    @23
    @9
    @1
    lmiopp.g
    ad2antrr
    ad2antrr
    #
    adantr
    #
    @22
    cP
    cG
    cI
    cL
    @2
    cA
    lmiopp.p
    lmiopp.i
    lmiopp.l
    @25
    @15
    @20
    @19
    simprl
    #
    @10
    cA
    cP
    wcel
    #
    @13
    @12
    @21
    wph
    @27
    @9
    @1
    wph
    cD
    cP
    cG
    cI
    cL
    cA
    lmiopp.p
    lmiopp.l
    lmiopp.i
    lmiopp.g
    lmiopp.d
    lnperpex.a
    tglnpt
    ad2antrr
    ad3antrrr
    #
    @22
    cA
    @2
    @22
    cP
    cG
    cI
    cL
    cA
    @2
    lmiopp.p
    lmiopp.i
    lmiopp.l
    @25
    @28
    @26
    @22
    @16
    cD
    cG
    cL
    lmiopp.l
    @25
    @15
    @20
    @17
    @18
    simprrl
    #
    perpln1
    tglnne
    necomd
    #
    tgelrnln
    @15
    cD
    cL
    crn
    wcel
    #
    @21
    @10
    @31
    @13
    @12
    wph
    @31
    @9
    @1
    lmiopp.d
    ad2antrr
    ad2antrr
    #
    adantr
    #
    @22
    @3
    @16
    cD
    @4
    @22
    cP
    @2
    cA
    cG
    cI
    cL
    lmiopp.p
    lmiopp.i
    lmiopp.l
    @25
    @26
    @28
    @30
    tglinecom
    @29
    eqbrtrd
    perpcom
    @22
    @12
    @6
    @15
    @12
    @21
    @14
    @12
    simpr
    #
    adantr
    @22
    vt
    @2
    cQ
    @11
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    lmiopp.p
    lmiopp.i
    lmiopp.l
    lmiopp.o
    @25
    @33
    @26
    @15
    cQ
    cP
    wcel
    #
    @21
    @10
    @35
    @13
    @12
    wph
    @35
    @9
    @1
    lnperpex.q
    ad2antrr
    ad2antrr
    #
    adantr
    @15
    @13
    @21
    @10
    @13
    @12
    simplr
    #
    adantr
    #
    @22
    vt
    @11
    @2
    cD
    cP
    cG
    cI
    cL
    c.mi
    cO
    va
    vb
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.o
    lmiopp.l
    @33
    @25
    @38
    @26
    @15
    @20
    @17
    @18
    simprrr
    oppcom
    lnopp2hpgb
    mpbid
    jca
    @15
    vt
    cA
    @11
    cD
    cP
    cG
    cI
    cG
    chlg
    cfv
    #
    cL
    c.mi
    cO
    vp
    va
    vb
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.o
    lmiopp.l
    @32
    @24
    @39
    eqid
    @10
    cA
    cD
    wcel
    #
    @13
    @12
    wph
    @40
    @9
    @1
    lnperpex.a
    ad2antrr
    ad2antrr
    @37
    @15
    vt
    cQ
    @11
    cD
    cP
    cG
    cI
    cL
    c.mi
    cO
    va
    vb
    lmiopp.p
    lmiopp.m
    lmiopp.i
    lmiopp.o
    lmiopp.l
    @32
    @24
    @36
    @37
    @34
    oppne2
    @10
    cG
    c2
    cstrkgld
    wbr
    #
    @13
    @12
    wph
    @41
    @9
    @1
    lmiopp.h
    ad2antrr
    ad2antrr
    oppperpex
    reximddv
    wph
    @12
    vc
    cP
    wrex
    @9
    @1
    wph
    vt
    cQ
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    vc
    lmiopp.p
    lmiopp.i
    lmiopp.l
    lmiopp.g
    lmiopp.d
    lnperpex.q
    lmiopp.o
    lnperpex.1
    hpgerlem
    ad2antrr
    r19.29a
    wph
    vd
    cD
    cP
    cG
    cI
    cL
    cA
    lmiopp.p
    lmiopp.i
    lmiopp.l
    lmiopp.g
    lmiopp.d
    lnperpex.a
    tglnpt2
    r19.29a
end
