include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "tglnne0.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "co.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "crn.mm"
include "simpr.mm"
include "tglnpt.mm"
include "c2.mm"
include "chash.mm"
include "cle.mm"
include "c1.mm"
include "wceq.mm"
include "wn.mm"
include "tglndim0.mm"
include "pm2.65da.mm"
include "cbs.mm"
include "tgldimor.mm"
include "ord.mm"
include "mpd.mm"
include "tgbtwndiff.mm"
include "ad4antr.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "btwnlng2.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "mtand.mm"
include "eleq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "jca31.mm"
include "anasss.mm"
include "wb.mm"
include "islnopp.mm"
include "mpbird.mm"
include "ex.mm"
include "reximdva.mm"
include "exlimddv.mm"

theorem hpgerlem
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let cB: class B
  assume hpgid.p: |- P = ( Base ` G )
  assume hpgid.i: |- I = ( Itv ` G )
  assume hpgid.l: |- L = ( LineG ` G )
  assume hpgid.g: |- ( ph -> G e. TarskiG )
  assume hpgid.d: |- ( ph -> D e. ran L )
  assume hpgid.a: |- ( ph -> A e. P )
  assume hpgid.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume hpgid.1: |- ( ph -> -. A e. D )

  disjoint A c
  disjoint A t
  disjoint c t
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D t
  disjoint a b
  disjoint a c
  disjoint a t
  disjoint b c
  disjoint b t
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P t
  disjoint c ph
  disjoint ph t
  disjoint A x
  disjoint c x
  disjoint t x
  disjoint B c
  disjoint B t
  disjoint D x
  disjoint a x
  disjoint b x
  disjoint O x
  disjoint P x
  disjoint ph x
  assert |- ( ph -> E. c e. P A O c )

  proof
    wph
    vx
    cv
    #
    cD
    wcel
    #
    cA
    vc
    cv
    #
    cO
    wbr
    #
    vc
    cP
    wrex
    #
    vx
    wph
    cD
    c0
    wne
    @1
    vx
    wex
    wph
    cD
    cG
    cL
    hpgid.l
    hpgid.g
    hpgid.d
    tglnne0
    vx
    cD
    n0
    sylib
    wph
    @1
    wa
    #
    @0
    cA
    @2
    cI
    co
    #
    wcel
    #
    @0
    @2
    wne
    #
    wa
    #
    vc
    cP
    wrex
    @4
    @5
    cA
    @0
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    vc
    hpgid.p
    @10
    eqid
    #
    hpgid.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    hpgid.g
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @1
    hpgid.a
    adantr
    #
    @5
    cD
    cP
    cG
    cI
    cL
    @0
    hpgid.p
    hpgid.l
    hpgid.i
    @13
    wph
    cD
    cL
    crn
    wcel
    #
    @1
    hpgid.d
    adantr
    #
    wph
    @1
    simpr
    #
    tglnpt
    #
    wph
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    @1
    wph
    @20
    c1
    wceq
    #
    wn
    @21
    wph
    @22
    @16
    wph
    @16
    @22
    hpgid.d
    adantr
    wph
    @22
    wa
    cD
    cP
    cG
    cI
    cL
    hpgid.p
    hpgid.i
    hpgid.l
    wph
    @12
    @22
    hpgid.g
    adantr
    wph
    @22
    simpr
    tglndim0
    pm2.65da
    wph
    @22
    @21
    wph
    cA
    cP
    cbs
    cG
    hpgid.p
    hpgid.a
    tgldimor
    ord
    mpd
    adantr
    tgbtwndiff
    @5
    @9
    @3
    vc
    cP
    @5
    @2
    cP
    wcel
    #
    wa
    #
    @9
    @3
    @24
    @9
    wa
    @3
    cA
    cD
    wcel
    #
    wn
    #
    @2
    cD
    wcel
    #
    wn
    #
    wa
    vt
    cv
    #
    @6
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    #
    @24
    @7
    @8
    @32
    @24
    @7
    wa
    #
    @8
    wa
    #
    @26
    @28
    @31
    wph
    @26
    @1
    @23
    @7
    @8
    hpgid.1
    ad4antr
    #
    @34
    @27
    @25
    @35
    @34
    @27
    wa
    #
    cA
    @0
    @2
    cL
    co
    cD
    @36
    cP
    cG
    cI
    cL
    @0
    @2
    cA
    hpgid.p
    hpgid.i
    hpgid.l
    @5
    @12
    @23
    @7
    @8
    @27
    @13
    ad4antr
    #
    @5
    @0
    cP
    wcel
    @23
    @7
    @8
    @27
    @19
    ad4antr
    #
    @24
    @23
    @7
    @8
    @27
    @5
    @23
    simpr
    #
    ad3antrrr
    #
    @24
    @14
    @7
    @8
    @27
    @5
    @14
    @23
    @15
    adantr
    #
    ad3antrrr
    @33
    @8
    @27
    simplr
    #
    @34
    @7
    @27
    @24
    @7
    @8
    simplr
    #
    adantr
    btwnlng2
    @36
    cD
    cP
    @0
    @2
    cG
    cI
    cL
    hpgid.p
    hpgid.i
    hpgid.l
    @37
    @38
    @40
    @42
    @42
    @5
    @16
    @23
    @7
    @8
    @27
    @17
    ad4antr
    @34
    @1
    @27
    @5
    @1
    @23
    @7
    @8
    @18
    ad3antrrr
    #
    adantr
    @34
    @27
    simpr
    tglinethru
    eleqtrrd
    mtand
    @34
    @1
    @7
    @31
    @44
    @43
    @30
    @7
    vt
    @0
    cD
    @29
    @0
    @6
    eleq1
    rspcev
    syl2anc
    jca31
    anasss
    @24
    @3
    @32
    wb
    @9
    @24
    vt
    cA
    @2
    cD
    cP
    cG
    cI
    @10
    cO
    va
    vb
    hpgid.p
    @11
    hpgid.i
    hpgid.o
    @41
    @39
    islnopp
    adantr
    mpbird
    ex
    reximdva
    mpd
    exlimddv
end
