include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "wb.mm"
include "xsubge0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "jca.mm"
include "elxrge0.mm"
include "sylibr.mm"

theorem xrge0subcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrge0subcld.a: |- ( ph -> A e. ( 0 [,] +oo ) )
  assume xrge0subcld.b: |- ( ph -> B e. ( 0 [,] +oo ) )
  assume xrge0subcld.c: |- ( ph -> B <_ A )


  assert |- ( ph -> ( A +e -e B ) e. ( 0 [,] +oo ) )

  proof
    wph
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cxr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wa
    @1
    cc0
    cpnf
    cicc
    co
    #
    wcel
    wph
    @2
    @3
    wph
    cA
    @0
    wph
    @4
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    xrge0subcld.a
    sseldi
    #
    wph
    cB
    wph
    @4
    cxr
    cB
    @5
    xrge0subcld.b
    sseldi
    #
    xnegcld
    xaddcld
    wph
    @3
    cB
    cA
    cle
    wbr
    #
    xrge0subcld.c
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @3
    @8
    wb
    @6
    @7
    cA
    cB
    xsubge0
    syl2anc
    mpbird
    jca
    @1
    elxrge0
    sylibr
end
