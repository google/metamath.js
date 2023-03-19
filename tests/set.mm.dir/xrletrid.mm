include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "jca.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem xrletrid
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrletrid.1: |- ( ph -> A e. RR* )
  assume xrletrid.2: |- ( ph -> B e. RR* )
  assume xrletrid.3: |- ( ph -> A <_ B )
  assume xrletrid.4: |- ( ph -> B <_ A )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wceq
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    #
    wph
    @1
    @2
    xrletrid.3
    xrletrid.4
    jca
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @3
    wb
    xrletrid.1
    xrletrid.2
    cA
    cB
    xrletri3
    syl2anc
    mpbird
end
