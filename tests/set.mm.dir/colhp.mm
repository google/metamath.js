include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "chpg.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "cmir.mm"
include "co.mm"
include "w3a.mm"
include "cstrkg.mm"
include "adantr.mm"
include "crn.mm"
include "cds.mm"
include "eqid.mm"
include "tglnpt.mm"
include "mircl.mm"
include "wceq.mm"
include "wne.mm"
include "nelne2.mm"
include "sylan.mm"
include "necomd.mm"
include "neneqd.mm"
include "cv.mm"
include "wrex.mm"
include "simpr.mm"
include "mirmir.mm"
include "mirln.mm"
include "eqeltrrd.mm"
include "stoic1a.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "mirbtwn.mm"
include "tgbtwncom.mm"
include "rspcedvd.mm"
include "jca31.mm"
include "islnopp.mm"
include "mpbird.mm"
include "oppne3.mm"
include "btwnlng1.mm"
include "orcd.mm"
include "colcom.mm"
include "colrot1.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "wo.mm"
include "coltr.mm"
include "colopp.mm"
include "lnopp2hpgb.mm"
include "simpll.mm"
include "syl.mm"
include "simprr.mm"
include "syl2anc.mm"
include "simprl.mm"
include "mirhl2.mm"
include "hlcomd.mm"
include "jca.mm"
include "3adantr3.mm"
include "simpld.mm"
include "ad2antrr.mm"
include "btwnhl.mm"
include "hlln.mm"
include "hlne2.mm"
include "ad3antrrr.mm"
include "tglinethru.mm"
include "eleqtrrd.mm"
include "pm2.65da.mm"
include "3jca.mm"
include "impbida.mm"
include "3bitr3d.mm"
include "pm5.32da.mm"
include "adantrl.mm"
include "hpgne1.mm"
include "3bitr2rd.mm"

theorem colhp
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vc: setvar c
  let vx: setvar x
  assume hpgid.p: |- P = ( Base ` G )
  assume hpgid.i: |- I = ( Itv ` G )
  assume hpgid.l: |- L = ( LineG ` G )
  assume hpgid.g: |- ( ph -> G e. TarskiG )
  assume hpgid.d: |- ( ph -> D e. ran L )
  assume hpgid.a: |- ( ph -> A e. P )
  assume hpgid.o: |- O = { <. a , b >. | ( ( a e. ( P \ D ) /\ b e. ( P \ D ) ) /\ E. t e. D t e. ( a I b ) ) }
  assume colopp.b: |- ( ph -> B e. P )
  assume colopp.p: |- ( ph -> C e. D )
  assume colopp.1: |- ( ph -> ( C e. ( A L B ) \/ A = B ) )
  assume colhp.k: |- K = ( hlG ` G )

  disjoint C t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint A a
  disjoint A b
  disjoint C a
  disjoint C b
  disjoint ph t
  disjoint A t
  disjoint B t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint O a
  disjoint O b
  disjoint O t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint ph t
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint t y
  disjoint D y
  disjoint G y
  disjoint I y
  disjoint L y
  disjoint a y
  disjoint b y
  disjoint ph y
  disjoint A c
  disjoint A x
  disjoint c t
  disjoint c x
  disjoint t x
  disjoint B c
  disjoint D c
  disjoint D x
  disjoint a c
  disjoint a x
  disjoint b c
  disjoint b x
  disjoint G c
  disjoint I c
  disjoint O x
  disjoint P c
  disjoint P x
  disjoint c ph
  disjoint ph x
  assert |- ( ph -> ( A ( ( hpG ` G ) ` D ) B <-> ( A ( K ` C ) B /\ -. A e. D ) ) )

  proof
    wph
    cA
    cB
    cC
    cK
    cfv
    wbr
    #
    cA
    cD
    wcel
    #
    wn
    #
    wa
    #
    @2
    @0
    wa
    #
    @2
    cA
    cB
    cD
    cG
    chpg
    cfv
    cfv
    wbr
    #
    wa
    #
    @5
    @3
    @4
    wb
    wph
    @0
    @2
    ancom
    a1i
    wph
    @2
    @5
    @0
    wph
    @2
    wa
    #
    cB
    cA
    cC
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    cO
    wbr
    cC
    cB
    @10
    cI
    co
    wcel
    #
    cB
    cD
    wcel
    #
    wn
    #
    @10
    cD
    wcel
    #
    wn
    #
    w3a
    #
    @5
    @0
    @7
    vt
    cB
    @10
    cC
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    hpgid.p
    hpgid.i
    hpgid.l
    wph
    cG
    cstrkg
    wcel
    #
    @2
    hpgid.g
    adantr
    #
    wph
    cD
    cL
    crn
    wcel
    #
    @2
    hpgid.d
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @2
    colopp.b
    adantr
    #
    hpgid.o
    wph
    @10
    cP
    wcel
    #
    @2
    wph
    cC
    cP
    @8
    cG
    cI
    cL
    @9
    cG
    cds
    cfv
    #
    cA
    hpgid.p
    @24
    eqid
    #
    hpgid.i
    hpgid.l
    @8
    eqid
    #
    hpgid.g
    wph
    cD
    cP
    cG
    cI
    cL
    cC
    hpgid.p
    hpgid.l
    hpgid.i
    hpgid.g
    hpgid.d
    colopp.p
    tglnpt
    #
    @9
    eqid
    #
    hpgid.a
    mircl
    #
    adantr
    #
    wph
    cC
    cD
    wcel
    #
    @2
    colopp.p
    adantr
    @7
    cP
    cG
    cI
    cL
    cC
    cB
    @10
    hpgid.p
    hpgid.l
    hpgid.i
    @18
    wph
    cC
    cP
    wcel
    #
    @2
    @27
    adantr
    #
    @22
    @30
    @7
    @10
    cA
    cC
    cB
    cP
    cG
    cI
    cL
    hpgid.p
    hpgid.i
    hpgid.l
    @18
    @30
    wph
    cA
    cP
    wcel
    #
    @2
    hpgid.a
    adantr
    #
    @33
    @22
    @7
    cA
    cC
    wceq
    #
    wn
    @10
    cA
    cC
    cL
    co
    wcel
    #
    @7
    cA
    cC
    @7
    cC
    cA
    wph
    @31
    @2
    cC
    cA
    wne
    colopp.p
    cC
    cA
    cD
    nelne2
    sylan
    necomd
    #
    neneqd
    @7
    @36
    @37
    @7
    @37
    @36
    @7
    cP
    cG
    cI
    cL
    @10
    cA
    cC
    hpgid.p
    hpgid.l
    hpgid.i
    @18
    @30
    @35
    @33
    @7
    cP
    cG
    cI
    cL
    cA
    @10
    cC
    hpgid.p
    hpgid.l
    hpgid.i
    @18
    @35
    @30
    @33
    @7
    cC
    cA
    @10
    cL
    co
    wcel
    cA
    @10
    wceq
    @7
    cP
    cG
    cI
    cL
    cA
    @10
    cC
    hpgid.p
    hpgid.i
    hpgid.l
    @18
    @35
    @30
    @33
    @7
    vt
    cA
    @10
    cD
    cP
    cG
    cI
    cL
    @24
    cO
    va
    vb
    hpgid.p
    @25
    hpgid.i
    hpgid.o
    hpgid.l
    @20
    @18
    @35
    @30
    @7
    cA
    @10
    cO
    wbr
    @2
    @15
    wa
    vt
    cv
    #
    cA
    @10
    cI
    co
    #
    wcel
    #
    vt
    cD
    wrex
    #
    wa
    @7
    @2
    @15
    @42
    wph
    @2
    simpr
    #
    wph
    @14
    @1
    wph
    @14
    wa
    #
    @10
    @9
    cfv
    #
    cA
    cD
    wph
    @45
    cA
    wceq
    @14
    wph
    cC
    cA
    cP
    @8
    cG
    cI
    cL
    @9
    @24
    hpgid.p
    @25
    hpgid.i
    hpgid.l
    @26
    hpgid.g
    @27
    @28
    hpgid.a
    mirmir
    adantr
    @44
    cC
    @10
    cD
    cP
    @8
    cG
    cI
    cL
    @9
    @24
    hpgid.p
    @25
    hpgid.i
    hpgid.l
    @26
    wph
    @17
    @14
    hpgid.g
    adantr
    @28
    wph
    @19
    @14
    hpgid.d
    adantr
    wph
    @31
    @14
    colopp.p
    adantr
    wph
    @14
    simpr
    mirln
    eqeltrrd
    stoic1a
    #
    wph
    @42
    @2
    wph
    @41
    cC
    @40
    wcel
    #
    vt
    cC
    cD
    colopp.p
    wph
    @39
    cC
    wceq
    #
    wa
    #
    @39
    cC
    @40
    @40
    wph
    @48
    simpr
    @49
    @40
    eqidd
    eleq12d
    wph
    @10
    cC
    cA
    cP
    cG
    cI
    @24
    hpgid.p
    @25
    hpgid.i
    hpgid.g
    @29
    @27
    hpgid.a
    wph
    cC
    cA
    cP
    @8
    cG
    cI
    cL
    @9
    @24
    hpgid.p
    @25
    hpgid.i
    hpgid.l
    @26
    hpgid.g
    @27
    @28
    hpgid.a
    mirbtwn
    tgbtwncom
    #
    rspcedvd
    adantr
    jca31
    @7
    vt
    cA
    @10
    cD
    cP
    cG
    cI
    @24
    cO
    va
    vb
    hpgid.p
    @25
    hpgid.i
    hpgid.o
    @35
    @30
    islnopp
    mpbird
    #
    oppne3
    wph
    @47
    @2
    @50
    adantr
    btwnlng1
    orcd
    colcom
    colrot1
    orcomd
    ord
    mpd
    wph
    cA
    cC
    cB
    cL
    co
    wcel
    cC
    cB
    wceq
    wo
    @2
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    hpgid.p
    hpgid.l
    hpgid.i
    hpgid.g
    colopp.b
    @27
    hpgid.a
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    hpgid.p
    hpgid.l
    hpgid.i
    hpgid.g
    hpgid.a
    colopp.b
    @27
    colopp.1
    colrot1
    colcom
    adantr
    coltr
    colrot1
    colopp
    @7
    vt
    cA
    cB
    @10
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.o
    @18
    @20
    @35
    @22
    @30
    @51
    lnopp2hpgb
    @7
    @16
    @0
    @7
    @16
    wa
    @0
    @2
    @7
    @11
    @13
    @3
    @15
    @7
    @11
    @13
    wa
    #
    wa
    #
    @0
    @2
    @53
    cB
    cA
    cC
    cP
    cG
    cI
    cK
    cstrkg
    hpgid.p
    hpgid.i
    colhp.k
    @53
    wph
    @21
    wph
    @2
    @52
    simpll
    #
    colopp.b
    syl
    #
    @53
    wph
    @34
    @54
    hpgid.a
    syl
    #
    @53
    wph
    @32
    @54
    @27
    syl
    #
    @53
    wph
    @17
    @54
    hpgid.g
    syl
    #
    @53
    cC
    cP
    @8
    cG
    cI
    cK
    cL
    @9
    @24
    cB
    cA
    cA
    hpgid.p
    @25
    hpgid.i
    hpgid.l
    @26
    @58
    @28
    colhp.k
    @57
    @55
    @56
    @56
    @53
    @31
    @13
    cB
    cC
    wne
    @53
    wph
    @31
    @54
    colopp.p
    syl
    @7
    @11
    @13
    simprr
    @31
    @13
    wa
    cC
    cB
    cC
    cB
    cD
    nelne2
    necomd
    syl2anc
    @7
    cA
    cC
    wne
    @52
    @38
    adantr
    @7
    @11
    @13
    simprl
    mirhl2
    hlcomd
    @7
    @2
    @52
    @43
    adantr
    jca
    3adantr3
    simpld
    @7
    @0
    wa
    #
    @11
    @13
    @15
    @59
    cA
    cB
    @10
    cC
    cP
    cG
    cI
    cK
    hpgid.p
    hpgid.i
    colhp.k
    @7
    @34
    @0
    @35
    adantr
    #
    @7
    @21
    @0
    @22
    adantr
    #
    @7
    @23
    @0
    @30
    adantr
    @7
    @17
    @0
    @18
    adantr
    #
    wph
    @32
    @2
    @0
    @27
    ad2antrr
    #
    @7
    @0
    simpr
    #
    wph
    @47
    @2
    @0
    @50
    ad2antrr
    btwnhl
    @59
    @12
    @1
    @59
    @12
    wa
    #
    cA
    cB
    cC
    cL
    co
    #
    cD
    @59
    cA
    @66
    wcel
    @12
    @59
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cL
    hpgid.p
    hpgid.i
    colhp.k
    @60
    @61
    @63
    @62
    hpgid.l
    @64
    hlln
    adantr
    @65
    cD
    cP
    cB
    cC
    cG
    cI
    cL
    hpgid.p
    hpgid.i
    hpgid.l
    @59
    @17
    @12
    @62
    adantr
    #
    @59
    @21
    @12
    @61
    adantr
    #
    @59
    @32
    @12
    @63
    adantr
    #
    @65
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cstrkg
    hpgid.p
    hpgid.i
    colhp.k
    @59
    @34
    @12
    @60
    adantr
    @68
    @69
    @67
    @59
    @0
    @12
    @64
    adantr
    hlne2
    #
    @70
    @7
    @19
    @0
    @12
    @20
    ad2antrr
    @59
    @12
    simpr
    wph
    @31
    @2
    @0
    @12
    colopp.p
    ad3antrrr
    tglinethru
    eleqtrrd
    @7
    @2
    @0
    @12
    @43
    ad2antrr
    pm2.65da
    @7
    @15
    @0
    @46
    adantr
    3jca
    impbida
    3bitr3d
    pm5.32da
    wph
    @6
    @5
    wph
    @5
    @5
    @2
    wph
    @5
    simpr
    #
    adantrl
    wph
    @5
    wa
    #
    @2
    @5
    @72
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    cO
    va
    vb
    hpgid.p
    hpgid.i
    hpgid.l
    hpgid.o
    wph
    @17
    @5
    hpgid.g
    adantr
    wph
    @19
    @5
    hpgid.d
    adantr
    wph
    @34
    @5
    hpgid.a
    adantr
    wph
    @21
    @5
    colopp.b
    adantr
    @71
    hpgne1
    @71
    jca
    impbida
    3bitr2rd
end
