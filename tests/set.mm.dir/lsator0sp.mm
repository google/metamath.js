include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "wne.mm"
include "lsatspn0.mm"
include "biimprd.mm"
include "necon1bd.mm"
include "clmod.mm"
include "wb.mm"
include "lspsneq0.mm"
include "syl2anc.mm"
include "sylibrd.mm"
include "orrd.mm"

theorem lsator0sp
  let wph: wff ph
  let cA: class A
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lsator0sp.v: |- V = ( Base ` W )
  assume lsator0sp.n: |- N = ( LSpan ` W )
  assume lsator0sp.o: |- .0. = ( 0g ` W )
  assume lsator0sp.a: |- A = ( LSAtoms ` W )
  assume isator0sp.w: |- ( ph -> W e. LMod )
  assume isator0sp.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( N ` { X } ) e. A \/ ( N ` { X } ) = { .0. } ) )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cA
    wcel
    #
    @0
    c.0
    csn
    wceq
    #
    wph
    @1
    wn
    cX
    c.0
    wceq
    #
    @2
    wph
    @1
    cX
    c.0
    wph
    @1
    cX
    c.0
    wne
    wph
    cA
    cN
    cV
    cW
    cX
    c.0
    lsator0sp.v
    lsator0sp.n
    lsator0sp.o
    lsator0sp.a
    isator0sp.w
    isator0sp.x
    lsatspn0
    biimprd
    necon1bd
    wph
    cW
    clmod
    wcel
    cX
    cV
    wcel
    @2
    @3
    wb
    isator0sp.w
    isator0sp.x
    cN
    cV
    cW
    cX
    c.0
    lsator0sp.v
    lsator0sp.o
    lsator0sp.n
    lspsneq0
    syl2anc
    sylibrd
    orrd
end
