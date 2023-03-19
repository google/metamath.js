include "ctsu.mm"
include "co.mm"
include "cuni.mm"
include "csn.mm"
include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wf.mm"
include "xrge0tsms2.mm"
include "syl2anc.mm"
include "en1eqsn.mm"
include "unieqd.mm"
include "unisng.mm"
include "syl.mm"
include "eqtr2d.mm"

theorem xrge0tsmseq
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cF: class F
  let cG: class G
  let cV: class V
  assume xrge0tsmseq.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0tsmseq.a: |- ( ph -> A e. V )
  assume xrge0tsmseq.f: |- ( ph -> F : A --> ( 0 [,] +oo ) )
  assume xrge0tsmseq.h: |- ( ph -> C e. ( G tsums F ) )


  assert |- ( ph -> C = U. ( G tsums F ) )

  proof
    wph
    cG
    cF
    ctsu
    co
    #
    cuni
    cC
    csn
    #
    cuni
    #
    cC
    wph
    @0
    @1
    wph
    cC
    @0
    wcel
    #
    @0
    c1o
    cen
    wbr
    #
    @0
    @1
    wceq
    xrge0tsmseq.h
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
    @4
    xrge0tsmseq.a
    xrge0tsmseq.f
    cA
    cF
    cG
    cV
    xrge0tsmseq.g
    xrge0tsms2
    syl2anc
    cC
    @0
    en1eqsn
    syl2anc
    unieqd
    wph
    @3
    @2
    cC
    wceq
    xrge0tsmseq.h
    cC
    @0
    unisng
    syl
    eqtr2d
end
