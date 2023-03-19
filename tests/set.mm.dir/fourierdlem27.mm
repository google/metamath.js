include "cv.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "cr.mm"
include "elioore.mm"
include "adantl.mm"
include "cicc.mm"
include "iccssxr.mm"
include "cc0.mm"
include "cfz.mm"
include "cfzo.mm"
include "elfzofz.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "rexrd.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "clt.mm"
include "fzofzp1.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "xrlelttrd.mm"
include "iooltub.mm"
include "iccleub.mm"
include "xrltletrd.mm"
include "eliood.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem fourierdlem27
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cI: class I
  let cM: class M
  let vx: setvar x
  let vk: setvar k
  assume fourierdlem27.a: |- ( ph -> A e. RR* )
  assume fourierdlem27.b: |- ( ph -> B e. RR* )
  assume fourierdlem27.q: |- ( ph -> Q : ( 0 ... M ) --> ( A [,] B ) )
  assume fourierdlem27.i: |- ( ph -> I e. ( 0 ..^ M ) )


  assert |- ( ph -> ( ( Q ` I ) (,) ( Q ` ( I + 1 ) ) ) C_ ( A (,) B ) )

  proof
    wph
    vx
    cv
    #
    cA
    cB
    cioo
    co
    #
    wcel
    #
    vx
    cI
    cQ
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cioo
    co
    #
    wral
    @6
    @1
    wss
    wph
    @2
    vx
    @6
    wph
    @0
    @6
    wcel
    #
    wa
    #
    cA
    cB
    @0
    wph
    cA
    cxr
    wcel
    #
    @7
    fourierdlem27.a
    adantr
    #
    wph
    cB
    cxr
    wcel
    #
    @7
    fourierdlem27.b
    adantr
    #
    @7
    @0
    cr
    wcel
    wph
    @0
    @3
    @5
    elioore
    adantl
    #
    @8
    cA
    @3
    @0
    @10
    wph
    @3
    cxr
    wcel
    #
    @7
    wph
    cA
    cB
    cicc
    co
    #
    cxr
    @3
    cA
    cB
    iccssxr
    #
    wph
    cc0
    cM
    cfz
    co
    #
    @15
    cI
    cQ
    fourierdlem27.q
    wph
    cI
    cc0
    cM
    cfzo
    co
    wcel
    #
    cI
    @17
    wcel
    fourierdlem27.i
    cI
    cc0
    cM
    elfzofz
    syl
    ffvelrnd
    #
    sseldi
    adantr
    #
    @8
    @0
    @13
    rexrd
    #
    wph
    cA
    @3
    cle
    wbr
    #
    @7
    wph
    @9
    @11
    @3
    @15
    wcel
    @22
    fourierdlem27.a
    fourierdlem27.b
    @19
    cA
    cB
    @3
    iccgelb
    syl3anc
    adantr
    @8
    @14
    @5
    cxr
    wcel
    #
    @7
    @3
    @0
    clt
    wbr
    @20
    wph
    @23
    @7
    wph
    @15
    cxr
    @5
    @16
    wph
    @17
    @15
    @4
    cQ
    fourierdlem27.q
    wph
    @18
    @4
    @17
    wcel
    fourierdlem27.i
    cc0
    cM
    cI
    fzofzp1
    syl
    ffvelrnd
    #
    sseldi
    adantr
    #
    wph
    @7
    simpr
    #
    @3
    @5
    @0
    ioogtlb
    syl3anc
    xrlelttrd
    @8
    @0
    @5
    cB
    @21
    @25
    @12
    @8
    @14
    @23
    @7
    @0
    @5
    clt
    wbr
    @20
    @25
    @26
    @3
    @5
    @0
    iooltub
    syl3anc
    wph
    @5
    cB
    cle
    wbr
    #
    @7
    wph
    @9
    @11
    @5
    @15
    wcel
    @27
    fourierdlem27.a
    fourierdlem27.b
    @24
    cA
    cB
    @5
    iccleub
    syl3anc
    adantr
    xrltletrd
    eliood
    ralrimiva
    vx
    @6
    @1
    dfss3
    sylibr
end
