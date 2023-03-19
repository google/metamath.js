include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cioc.mm"
include "cin.mm"
include "crest.mm"
include "ctop.mm"
include "wcel.mm"
include "cvv.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ovexd.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "cv.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "rexrd.mm"
include "cr.mm"
include "elinel1.mm"
include "elioore.mm"
include "syl.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "pnfxr.mm"
include "ioogtlb.mm"
include "cle.mm"
include "elinel2.mm"
include "iocleub.mm"
include "eliocd.mm"
include "wss.mm"
include "iocssre.mm"
include "syl2anc.mm"
include "sselda.mm"
include "simpr.mm"
include "iocgtlb.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "xrlelttrd.mm"
include "elind.mm"
include "impbida.mm"
include "eqrdv.mm"
include "wceq.mm"
include "eqcomi.mm"
include "3eltr3d.mm"

theorem iocopn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let vx: setvar x
  assume iocopn.a: |- ( ph -> A e. RR* )
  assume iocopn.c: |- ( ph -> C e. RR* )
  assume iocopn.b: |- ( ph -> B e. RR )
  assume iocopn.k: |- K = ( topGen ` ran (,) )
  assume iocopn.j: |- J = ( K |`t ( A (,] B ) )
  assume iocopn.alec: |- ( ph -> A <_ C )
  assume iocopn.6: |- ( ph -> B e. RR )


  assert |- ( ph -> ( C (,] B ) e. J )

  proof
    wph
    cC
    cpnf
    cioo
    co
    #
    cA
    cB
    cioc
    co
    #
    cin
    #
    cK
    @1
    crest
    co
    #
    cC
    cB
    cioc
    co
    #
    cJ
    wph
    cK
    ctop
    wcel
    #
    @1
    cvv
    wcel
    @0
    cK
    wcel
    #
    @2
    @3
    wcel
    @5
    wph
    cK
    cioo
    crn
    ctg
    cfv
    #
    ctop
    iocopn.k
    retop
    eqeltri
    a1i
    wph
    cA
    cB
    cioc
    ovexd
    @6
    wph
    @0
    @7
    cK
    cC
    cpnf
    iooretop
    iocopn.k
    eleqtrri
    a1i
    @0
    @1
    cK
    ctop
    cvv
    elrestr
    syl3anc
    wph
    vx
    @2
    @4
    wph
    vx
    cv
    #
    @2
    wcel
    #
    @8
    @4
    wcel
    #
    wph
    @9
    wa
    #
    cC
    cB
    @8
    wph
    cC
    cxr
    wcel
    #
    @9
    iocopn.c
    adantr
    #
    wph
    cB
    cxr
    wcel
    #
    @9
    wph
    cB
    iocopn.b
    rexrd
    #
    adantr
    #
    @9
    @8
    cxr
    wcel
    wph
    @9
    @8
    @9
    @8
    @0
    wcel
    #
    @8
    cr
    wcel
    @8
    @0
    @1
    elinel1
    #
    @8
    cC
    cpnf
    elioore
    syl
    rexrd
    adantl
    @11
    @12
    cpnf
    cxr
    wcel
    #
    @17
    cC
    @8
    clt
    wbr
    #
    @13
    @19
    @11
    pnfxr
    a1i
    @9
    @17
    wph
    @18
    adantl
    cC
    cpnf
    @8
    ioogtlb
    syl3anc
    @11
    cA
    cxr
    wcel
    #
    @14
    @8
    @1
    wcel
    #
    @8
    cB
    cle
    wbr
    #
    wph
    @21
    @9
    iocopn.a
    adantr
    @16
    @9
    @22
    wph
    @8
    @0
    @1
    elinel2
    adantl
    cA
    cB
    @8
    iocleub
    syl3anc
    eliocd
    wph
    @10
    wa
    #
    @0
    @1
    @8
    @24
    cC
    cpnf
    @8
    wph
    @12
    @10
    iocopn.c
    adantr
    #
    @19
    @24
    pnfxr
    a1i
    wph
    @4
    cr
    @8
    wph
    @12
    cB
    cr
    wcel
    @4
    cr
    wss
    iocopn.c
    iocopn.6
    cC
    cB
    iocssre
    syl2anc
    sselda
    #
    @24
    @12
    @14
    @10
    @20
    @25
    wph
    @14
    @10
    @15
    adantr
    #
    wph
    @10
    simpr
    #
    cC
    cB
    @8
    iocgtlb
    syl3anc
    #
    @24
    @8
    @26
    ltpnfd
    eliood
    @24
    cA
    cB
    @8
    wph
    @21
    @10
    iocopn.a
    adantr
    #
    @27
    @24
    @8
    @26
    rexrd
    #
    @24
    cA
    cC
    @8
    @30
    @25
    @31
    wph
    cA
    cC
    cle
    wbr
    @10
    iocopn.alec
    adantr
    @29
    xrlelttrd
    @24
    @12
    @14
    @10
    @23
    @25
    @27
    @28
    cC
    cB
    @8
    iocleub
    syl3anc
    eliocd
    elind
    impbida
    eqrdv
    @3
    cJ
    wceq
    wph
    cJ
    @3
    iocopn.j
    eqcomi
    a1i
    3eltr3d
end
