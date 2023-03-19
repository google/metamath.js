include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "csn.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "xrge0tsms2.mm"
include "syl2anc.mm"
include "en1b.mm"
include "sylib.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "uniex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "elsng.mm"
include "syl.mm"
include "ibir.mm"
include "elsni.mm"
include "impbii.mm"
include "syl6bbr.mm"

theorem xrge0tsmsbi
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cF: class F
  let cG: class G
  let cV: class V
  assume xrge0tsmseq.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0tsmseq.a: |- ( ph -> A e. V )
  assume xrge0tsmseq.f: |- ( ph -> F : A --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( C e. ( G tsums F ) <-> C = U. ( G tsums F ) ) )

  proof
    wph
    cC
    cG
    cF
    ctsu
    co
    #
    wcel
    cC
    @0
    cuni
    #
    csn
    #
    wcel
    #
    cC
    @1
    wceq
    #
    wph
    @0
    @2
    cC
    wph
    @0
    c1o
    cen
    wbr
    #
    @0
    @2
    wceq
    wph
    cA
    cV
    wcel
    cA
    cc0
    cpnf
    cicc
    co
    cF
    wf
    @5
    xrge0tsmseq.a
    xrge0tsmseq.f
    cA
    cF
    cG
    cV
    xrge0tsmseq.g
    xrge0tsms2
    syl2anc
    @0
    en1b
    sylib
    eleq2d
    @4
    @3
    @4
    @3
    @4
    cC
    cvv
    wcel
    #
    @3
    @4
    wb
    @4
    @6
    @1
    cvv
    wcel
    @0
    cG
    cF
    ctsu
    ovex
    uniex
    cC
    @1
    cvv
    eleq1
    mpbiri
    cC
    @1
    cvv
    elsng
    syl
    ibir
    cC
    @1
    elsni
    impbii
    syl6bbr
end
