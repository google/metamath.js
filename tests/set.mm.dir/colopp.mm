include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "wbr.mm"
include "w3a.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "crn.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprd.mm"
include "simplr.mm"
include "wceq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "simpr.mm"
include "rspcedvd.mm"
include "jca31.mm"
include "islnopp.mm"
include "mpbird.mm"
include "oppne3.mm"
include "tgelrnln.mm"
include "wne.mm"
include "tglinerflx1.mm"
include "oppne1.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "wi.mm"
include "orcomd.mm"
include "ord.mm"
include "mpd.mm"
include "elind.mm"
include "tglnpt.mm"
include "btwnlng1.mm"
include "tglineineq.mm"
include "eqeltrd.mm"
include "adantllr.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "r19.29a.mm"
include "adantr.mm"
include "eleq1d.mm"
include "adantlr.mm"
include "impbida.mm"
include "pm5.32da.mm"
include "3anrot.mm"
include "df-3an.mm"
include "bitri.mm"
include "a1i.mm"
include "3bitr4d.mm"

theorem colopp
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
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

  disjoint C t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint a b
  disjoint a t
  disjoint b t
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
  assert |- ( ph -> ( A O B <-> ( C e. ( A I B ) /\ -. A e. D /\ -. B e. D ) ) )

  proof
    wph
    cA
    cD
    wcel
    wn
    #
    cB
    cD
    wcel
    wn
    #
    wa
    #
    vt
    cv
    #
    cA
    cB
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
    #
    @2
    cC
    @4
    wcel
    #
    wa
    #
    cA
    cB
    cO
    wbr
    #
    @8
    @0
    @1
    w3a
    #
    wph
    @2
    @6
    @8
    wph
    @2
    wa
    #
    @6
    @8
    @12
    @6
    wa
    #
    vy
    cv
    #
    @4
    wcel
    #
    @8
    vy
    cD
    @12
    @14
    cD
    wcel
    #
    @15
    @8
    @6
    @12
    @16
    wa
    #
    @15
    wa
    #
    cC
    @14
    @4
    @18
    cA
    cB
    cL
    co
    #
    cD
    cP
    cG
    cI
    cL
    cC
    @14
    hpgid.p
    hpgid.i
    hpgid.l
    wph
    cG
    cstrkg
    wcel
    @2
    @16
    @15
    hpgid.g
    ad3antrrr
    #
    @18
    cP
    cG
    cI
    cL
    cA
    cB
    hpgid.p
    hpgid.i
    hpgid.l
    @20
    wph
    cA
    cP
    wcel
    @2
    @16
    @15
    hpgid.a
    ad3antrrr
    #
    wph
    cB
    cP
    wcel
    @2
    @16
    @15
    colopp.b
    ad3antrrr
    #
    @18
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    cG
    cds
    cfv
    #
    cO
    va
    vb
    hpgid.p
    @23
    eqid
    #
    hpgid.i
    hpgid.o
    hpgid.l
    wph
    cD
    cL
    crn
    wcel
    @2
    @16
    @15
    hpgid.d
    ad3antrrr
    #
    @20
    @21
    @22
    @18
    @10
    @7
    @18
    @0
    @1
    @6
    @18
    @0
    @1
    wph
    @2
    @16
    @15
    simpllr
    #
    simpld
    @18
    @0
    @1
    @26
    simprd
    @18
    @5
    @15
    vt
    @14
    cD
    @12
    @16
    @15
    simplr
    #
    @3
    @14
    wceq
    @5
    @15
    wb
    @18
    @3
    @14
    @4
    eleq1
    #
    adantl
    @17
    @15
    simpr
    #
    rspcedvd
    jca31
    wph
    @10
    @7
    wb
    @2
    @16
    @15
    wph
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    @23
    cO
    va
    vb
    hpgid.p
    @24
    hpgid.i
    hpgid.o
    hpgid.a
    colopp.b
    islnopp
    #
    ad3antrrr
    mpbird
    #
    oppne3
    #
    tgelrnln
    @25
    @18
    cA
    @19
    wcel
    @0
    @19
    cD
    wne
    @18
    cP
    cA
    cB
    cG
    cI
    cL
    hpgid.p
    hpgid.i
    hpgid.l
    @20
    @21
    @22
    @32
    tglinerflx1
    @18
    vt
    cA
    cB
    cD
    cP
    cG
    cI
    cL
    @23
    cO
    va
    vb
    hpgid.p
    @24
    hpgid.i
    hpgid.o
    hpgid.l
    @25
    @20
    @21
    @22
    @31
    oppne1
    cA
    @19
    cD
    nelne1
    syl2anc
    @18
    @19
    cD
    cC
    @18
    cA
    cB
    wceq
    #
    wn
    #
    cC
    @19
    wcel
    #
    @18
    cA
    cB
    @32
    neneqd
    wph
    @34
    @35
    wi
    @2
    @16
    @15
    wph
    @33
    @35
    wph
    @35
    @33
    colopp.1
    orcomd
    ord
    ad3antrrr
    mpd
    wph
    cC
    cD
    wcel
    #
    @2
    @16
    @15
    colopp.p
    ad3antrrr
    elind
    @18
    @19
    cD
    @14
    @18
    cP
    cG
    cI
    cL
    cA
    cB
    @14
    hpgid.p
    hpgid.i
    hpgid.l
    @20
    @21
    @22
    @18
    cD
    cP
    cG
    cI
    cL
    @14
    hpgid.p
    hpgid.l
    hpgid.i
    @20
    @25
    @27
    tglnpt
    @32
    @29
    btwnlng1
    @27
    elind
    tglineineq
    @29
    eqeltrd
    adantllr
    @13
    @6
    @15
    vy
    cD
    wrex
    @12
    @6
    simpr
    @5
    @15
    vt
    vy
    cD
    @28
    cbvrexv
    sylib
    r19.29a
    wph
    @8
    @6
    @2
    wph
    @8
    wa
    #
    @5
    @8
    vt
    cC
    cD
    wph
    @36
    @8
    colopp.p
    adantr
    @37
    @3
    cC
    wceq
    #
    wa
    @3
    cC
    @4
    @37
    @38
    simpr
    eleq1d
    wph
    @8
    simpr
    rspcedvd
    adantlr
    impbida
    pm5.32da
    @30
    @11
    @9
    wb
    wph
    @11
    @0
    @1
    @8
    w3a
    @9
    @8
    @0
    @1
    3anrot
    @0
    @1
    @8
    df-3an
    bitri
    a1i
    3bitr4d
end
