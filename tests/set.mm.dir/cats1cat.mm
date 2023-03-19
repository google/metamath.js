include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "oveq1i.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "s1cli.mm"
include "ccatass.mm"
include "mp3an.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem cats1cat
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cX: class X
  assume cats1cld.1: |- T = ( S ++ <" X "> )
  assume cats1cat.2: |- A e. Word _V
  assume cats1cat.3: |- S e. Word _V
  assume cats1cat.4: |- C = ( B ++ <" X "> )
  assume cats1cat.5: |- B = ( A ++ S )


  assert |- C = ( A ++ T )

  proof
    cB
    cX
    cs1
    #
    cconcat
    co
    #
    cA
    cS
    @0
    cconcat
    co
    #
    cconcat
    co
    #
    cC
    cA
    cT
    cconcat
    co
    @1
    cA
    cS
    cconcat
    co
    #
    @0
    cconcat
    co
    #
    @3
    cB
    @4
    @0
    cconcat
    cats1cat.5
    oveq1i
    cA
    cvv
    cword
    #
    wcel
    cS
    @6
    wcel
    @0
    @6
    wcel
    @5
    @3
    wceq
    cats1cat.2
    cats1cat.3
    cX
    s1cli
    cvv
    cA
    cS
    @0
    ccatass
    mp3an
    eqtri
    cats1cat.4
    cT
    @2
    cA
    cconcat
    cats1cld.1
    oveq2i
    3eqtr4i
end
