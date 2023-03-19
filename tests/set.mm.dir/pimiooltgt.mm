include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "cxr.mm"
include "adantr.mm"
include "3adant3.mm"
include "simp3.mm"
include "iooltub.mm"
include "syl3anc.mm"
include "3exp.mm"
include "ralrimi.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "ioogtlb.mm"
include "ssind.mm"
include "wa.mm"
include "elinel1.mm"
include "ssrab2.mm"
include "sseli.mm"
include "syl.mm"
include "adantl.mm"
include "syldan.mm"
include "cmnf.mm"
include "mnfxr.mm"
include "a1i.mm"
include "mnfled.mm"
include "elinel2.mm"
include "rabidim2.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "necomd.mm"
include "cpnf.mm"
include "pnfxr.mm"
include "cle.mm"
include "pnfge.mm"
include "xrltletrd.mm"
include "xrred.mm"
include "eliood.mm"
include "jca.mm"
include "rabid.mm"
include "ex.mm"
include "nfrab1.mm"
include "nfin.mm"
include "dfss3f.mm"
include "eqssd.mm"

theorem pimiooltgt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cL: class L
  let vk: setvar k
  assume pimiooltgt.1: |- F/ x ph
  assume pimiooltgt.2: |- ( ph -> L e. RR* )
  assume pimiooltgt.3: |- ( ph -> R e. RR* )
  assume pimiooltgt.4: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A x
  disjoint k x
  assert |- ( ph -> { x e. A | B e. ( L (,) R ) } = ( { x e. A | B < R } i^i { x e. A | L < B } ) )

  proof
    wph
    cB
    cL
    cR
    cioo
    co
    wcel
    #
    vx
    cA
    crab
    #
    cB
    cR
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cL
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cin
    #
    wph
    @1
    @3
    @5
    wph
    @0
    @2
    wi
    #
    vx
    cA
    wral
    @1
    @3
    wss
    wph
    @7
    vx
    cA
    pimiooltgt.1
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    @2
    wph
    @9
    @0
    w3a
    #
    cL
    cxr
    wcel
    #
    cR
    cxr
    wcel
    #
    @0
    @2
    wph
    @9
    @11
    @0
    wph
    @11
    @9
    pimiooltgt.2
    adantr
    #
    3adant3
    #
    wph
    @9
    @12
    @0
    wph
    @12
    @9
    pimiooltgt.3
    adantr
    #
    3adant3
    #
    wph
    @9
    @0
    simp3
    #
    cL
    cR
    cB
    iooltub
    syl3anc
    3exp
    ralrimi
    @0
    @2
    vx
    cA
    ss2rab
    sylibr
    wph
    @0
    @4
    wi
    #
    vx
    cA
    wral
    @1
    @5
    wss
    wph
    @18
    vx
    cA
    pimiooltgt.1
    wph
    @9
    @0
    @4
    @10
    @11
    @12
    @0
    @4
    @14
    @16
    @17
    cL
    cR
    cB
    ioogtlb
    syl3anc
    3exp
    ralrimi
    @0
    @4
    vx
    cA
    ss2rab
    sylibr
    ssind
    wph
    @8
    @1
    wcel
    #
    vx
    @6
    wral
    @6
    @1
    wss
    wph
    @19
    vx
    @6
    pimiooltgt.1
    wph
    @8
    @6
    wcel
    #
    @19
    wph
    @20
    wa
    #
    @9
    @0
    wa
    @19
    @21
    @9
    @0
    @20
    @9
    wph
    @20
    @8
    @3
    wcel
    #
    @9
    @8
    @3
    @5
    elinel1
    #
    @3
    cA
    @8
    @2
    vx
    cA
    ssrab2
    sseli
    syl
    adantl
    #
    @21
    cL
    cR
    cB
    wph
    @20
    @9
    @11
    @24
    @13
    syldan
    #
    wph
    @20
    @9
    @12
    @24
    @15
    syldan
    #
    @21
    cB
    wph
    @20
    @9
    cB
    cxr
    wcel
    @24
    pimiooltgt.4
    syldan
    #
    @21
    cmnf
    cB
    @21
    cmnf
    cB
    cmnf
    cxr
    wcel
    @21
    mnfxr
    a1i
    #
    @27
    @21
    cmnf
    cL
    cB
    @28
    @25
    @27
    @21
    cL
    @25
    mnfled
    @20
    @4
    wph
    @20
    @8
    @5
    wcel
    @4
    @8
    @3
    @5
    elinel2
    @4
    vx
    cA
    rabidim2
    syl
    adantl
    #
    xrlelttrd
    xrltned
    necomd
    @21
    cB
    cpnf
    @27
    cpnf
    cxr
    wcel
    @21
    pnfxr
    a1i
    #
    @21
    cB
    cR
    cpnf
    @27
    @26
    @30
    @20
    @2
    wph
    @20
    @22
    @2
    @23
    @2
    vx
    cA
    rabidim2
    syl
    adantl
    #
    @21
    @12
    cR
    cpnf
    cle
    wbr
    @26
    cR
    pnfge
    syl
    xrltletrd
    xrltned
    xrred
    @29
    @31
    eliood
    jca
    @0
    vx
    cA
    rabid
    sylibr
    ex
    ralrimi
    vx
    @6
    @1
    vx
    @3
    @5
    @2
    vx
    cA
    nfrab1
    @4
    vx
    cA
    nfrab1
    nfin
    @0
    vx
    cA
    nfrab1
    dfss3f
    sylibr
    eqssd
end
