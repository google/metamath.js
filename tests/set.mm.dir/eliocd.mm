include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "wb.mm"
include "elioc1.mm"
include "syl2anc.mm"
include "mpbir3and.mm"

theorem eliocd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliocd.a: |- ( ph -> A e. RR* )
  assume eliocd.b: |- ( ph -> B e. RR* )
  assume eliocd.c: |- ( ph -> C e. RR* )
  assume eliocd.altc: |- ( ph -> A < C )
  assume eliocd.cleb: |- ( ph -> C <_ B )


  assert |- ( ph -> C e. ( A (,] B ) )

  proof
    wph
    cC
    cA
    cB
    cioc
    co
    wcel
    #
    cC
    cxr
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    eliocd.c
    eliocd.altc
    eliocd.cleb
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @0
    @1
    @2
    @3
    w3a
    wb
    eliocd.a
    eliocd.b
    cA
    cB
    cC
    elioc1
    syl2anc
    mpbir3and
end
