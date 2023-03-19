include "cioc.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "leidd.mm"
include "ltled.mm"
include "eliccd.mm"
include "ad2antrr.mm"
include "wn.mm"
include "iocssicc.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "ifclda.mm"
include "fmptd.mm"

theorem fourierdlem17
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cL: class L
  let vk: setvar k
  assume fourierdlem17.a: |- ( ph -> A e. RR )
  assume fourierdlem17.b: |- ( ph -> B e. RR )
  assume fourierdlem17.altb: |- ( ph -> A < B )
  assume fourierdlem17.l: |- L = ( x e. ( A (,] B ) |-> if ( x = B , A , x ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> L : ( A (,] B ) --> ( A [,] B ) )

  proof
    wph
    vx
    cA
    cB
    cioc
    co
    #
    vx
    cv
    #
    cB
    wceq
    #
    cA
    @1
    cif
    cA
    cB
    cicc
    co
    #
    cL
    wph
    @1
    @0
    wcel
    #
    wa
    @2
    cA
    @1
    @3
    wph
    cA
    @3
    wcel
    @4
    @2
    wph
    cA
    cB
    cA
    fourierdlem17.a
    fourierdlem17.b
    fourierdlem17.a
    wph
    cA
    fourierdlem17.a
    leidd
    wph
    cA
    cB
    fourierdlem17.a
    fourierdlem17.b
    fourierdlem17.altb
    ltled
    eliccd
    ad2antrr
    @4
    @1
    @3
    wcel
    wph
    @2
    wn
    @0
    @3
    @1
    cA
    cB
    iocssicc
    sseli
    ad2antlr
    ifclda
    fourierdlem17.l
    fmptd
end
