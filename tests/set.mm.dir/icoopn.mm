include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cico.mm"
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
include "rexrd.mm"
include "adantr.mm"
include "cr.mm"
include "elinel1.mm"
include "elioore.mm"
include "syl.mm"
include "adantl.mm"
include "cle.mm"
include "wbr.mm"
include "elinel2.mm"
include "icogelb.mm"
include "clt.mm"
include "mnfxr.mm"
include "iooltub.mm"
include "elicod.mm"
include "wss.mm"
include "icossre.mm"
include "syl2anc.mm"
include "sselda.mm"
include "mnfltd.mm"
include "simpr.mm"
include "icoltub.mm"
include "eliood.mm"
include "xrltletrd.mm"
include "elind.mm"
include "impbida.mm"
include "eqrdv.mm"
include "wceq.mm"
include "eqcomi.mm"
include "3eltr3d.mm"

theorem icoopn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let vx: setvar x
  assume icoopn.a: |- ( ph -> A e. RR )
  assume icoopn.c: |- ( ph -> C e. RR* )
  assume icoopn.b: |- ( ph -> B e. RR* )
  assume icoopn.k: |- K = ( topGen ` ran (,) )
  assume icoopn.j: |- J = ( K |`t ( A [,) B ) )
  assume icoopn.cleb: |- ( ph -> C <_ B )


  assert |- ( ph -> ( A [,) C ) e. J )

  proof
    wph
    cmnf
    cC
    cioo
    co
    #
    cA
    cB
    cico
    co
    #
    cin
    #
    cK
    @1
    crest
    co
    #
    cA
    cC
    cico
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
    icoopn.k
    retop
    eqeltri
    a1i
    wph
    cA
    cB
    cico
    ovexd
    @6
    wph
    @0
    @7
    cK
    cmnf
    cC
    iooretop
    icoopn.k
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
    cA
    cC
    @8
    wph
    cA
    cxr
    wcel
    #
    @9
    wph
    cA
    icoopn.a
    rexrd
    #
    adantr
    #
    wph
    cC
    cxr
    wcel
    #
    @9
    icoopn.c
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
    cmnf
    cC
    elioore
    syl
    rexrd
    adantl
    @11
    @12
    cB
    cxr
    wcel
    #
    @8
    @1
    wcel
    #
    cA
    @8
    cle
    wbr
    #
    @14
    wph
    @19
    @9
    icoopn.b
    adantr
    @9
    @20
    wph
    @8
    @0
    @1
    elinel2
    adantl
    cA
    cB
    @8
    icogelb
    syl3anc
    @11
    cmnf
    cxr
    wcel
    #
    @15
    @17
    @8
    cC
    clt
    wbr
    #
    @22
    @11
    mnfxr
    a1i
    @16
    @9
    @17
    wph
    @18
    adantl
    cmnf
    cC
    @8
    iooltub
    syl3anc
    elicod
    wph
    @10
    wa
    #
    @0
    @1
    @8
    @24
    cmnf
    cC
    @8
    @22
    @24
    mnfxr
    a1i
    wph
    @15
    @10
    icoopn.c
    adantr
    #
    wph
    @4
    cr
    @8
    wph
    cA
    cr
    wcel
    @15
    @4
    cr
    wss
    icoopn.a
    icoopn.c
    cA
    cC
    icossre
    syl2anc
    sselda
    #
    @24
    @8
    @26
    mnfltd
    @24
    @12
    @15
    @10
    @23
    wph
    @12
    @10
    @13
    adantr
    #
    @25
    wph
    @10
    simpr
    #
    cA
    cC
    @8
    icoltub
    syl3anc
    #
    eliood
    @24
    cA
    cB
    @8
    @27
    wph
    @19
    @10
    icoopn.b
    adantr
    #
    @24
    @8
    @26
    rexrd
    #
    @24
    @12
    @15
    @10
    @21
    @27
    @25
    @28
    cA
    cC
    @8
    icogelb
    syl3anc
    @24
    @8
    cC
    cB
    @31
    @25
    @30
    @29
    wph
    cC
    cB
    cle
    wbr
    @10
    icoopn.cleb
    adantr
    xrltletrd
    elicod
    elind
    impbida
    eqrdv
    @3
    cJ
    wceq
    wph
    cJ
    @3
    icoopn.j
    eqcomi
    a1i
    3eltr3d
end
