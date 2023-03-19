include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "cc0.mm"
include "cfz.mm"
include "cfzo.mm"
include "elfzofz.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "wa.mm"
include "wb.mm"
include "fzofzp1.mm"
include "elicc4.mm"
include "mpbid.mm"
include "simpld.mm"
include "xrletrd.mm"
include "iccleub.mm"
include "simprd.mm"
include "w3a.mm"
include "elicc1.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem fourierdlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cI: class I
  let cM: class M
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem1.a: |- ( ph -> A e. RR* )
  assume fourierdlem1.b: |- ( ph -> B e. RR* )
  assume fourierdlem1.q: |- ( ph -> Q : ( 0 ... M ) --> ( A [,] B ) )
  assume fourierdlem1.i: |- ( ph -> I e. ( 0 ..^ M ) )
  assume fourierdlem1.x: |- ( ph -> X e. ( ( Q ` I ) [,] ( Q ` ( I + 1 ) ) ) )


  assert |- ( ph -> X e. ( A [,] B ) )

  proof
    wph
    cX
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cX
    cxr
    wcel
    #
    cA
    cX
    cle
    wbr
    #
    cX
    cB
    cle
    wbr
    #
    wph
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
    cicc
    co
    #
    cxr
    cX
    @5
    @7
    iccssxr
    fourierdlem1.x
    sseldi
    #
    wph
    cA
    @5
    cX
    fourierdlem1.a
    wph
    @0
    cxr
    @5
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
    @0
    cI
    cQ
    fourierdlem1.q
    wph
    cI
    cc0
    cM
    cfzo
    co
    wcel
    #
    cI
    @11
    wcel
    fourierdlem1.i
    cI
    cc0
    cM
    elfzofz
    syl
    ffvelrnd
    #
    sseldi
    #
    @9
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @5
    @0
    wcel
    cA
    @5
    cle
    wbr
    fourierdlem1.a
    fourierdlem1.b
    @13
    cA
    cB
    @5
    iccgelb
    syl3anc
    wph
    @5
    cX
    cle
    wbr
    #
    cX
    @7
    cle
    wbr
    #
    wph
    cX
    @8
    wcel
    #
    @17
    @18
    wa
    #
    fourierdlem1.x
    wph
    @5
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @2
    @19
    @20
    wb
    @14
    wph
    @0
    cxr
    @7
    @10
    wph
    @11
    @0
    @6
    cQ
    fourierdlem1.q
    wph
    @12
    @6
    @11
    wcel
    fourierdlem1.i
    cc0
    cM
    cI
    fzofzp1
    syl
    ffvelrnd
    #
    sseldi
    #
    @9
    @5
    @7
    cX
    elicc4
    syl3anc
    mpbid
    simpld
    xrletrd
    wph
    cX
    @7
    cB
    @9
    @24
    fourierdlem1.b
    wph
    @21
    @22
    @19
    @18
    @14
    @24
    fourierdlem1.x
    @5
    @7
    cX
    iccleub
    syl3anc
    wph
    cA
    @7
    cle
    wbr
    #
    @7
    cB
    cle
    wbr
    #
    wph
    @7
    @0
    wcel
    #
    @25
    @26
    wa
    #
    @23
    wph
    @15
    @16
    @22
    @27
    @28
    wb
    fourierdlem1.a
    fourierdlem1.b
    @24
    cA
    cB
    @7
    elicc4
    syl3anc
    mpbid
    simprd
    xrletrd
    wph
    @15
    @16
    @1
    @2
    @3
    @4
    w3a
    wb
    fourierdlem1.a
    fourierdlem1.b
    cA
    cB
    cX
    elicc1
    syl2anc
    mpbir3and
end
