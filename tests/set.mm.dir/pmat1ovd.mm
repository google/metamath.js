include "crg.mm"
include "wcel.mm"
include "ply1ring.mm"
include "syl.mm"
include "mat1ov.mm"

theorem pmat1ovd
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  assume pmatring.p: |- P = ( Poly1 ` R )
  assume pmatring.c: |- C = ( N Mat P )
  assume pmat0op.z: |- .0. = ( 0g ` P )
  assume pmat1op.o: |- .1. = ( 1r ` P )
  assume pmat1ovd.n: |- ( ph -> N e. Fin )
  assume pmat1ovd.r: |- ( ph -> R e. Ring )
  assume pmat1ovd.i: |- ( ph -> I e. N )
  assume pmat1ovd.j: |- ( ph -> J e. N )
  assume pmat1ovd.u: |- U = ( 1r ` C )


  assert |- ( ph -> ( I U J ) = if ( I = J , .1. , .0. ) )

  proof
    wph
    cC
    cP
    cU
    c.1
    cI
    cJ
    cN
    c.0
    pmatring.c
    pmat1op.o
    pmat0op.z
    pmat1ovd.n
    wph
    cR
    crg
    wcel
    cP
    crg
    wcel
    pmat1ovd.r
    cP
    cR
    pmatring.p
    ply1ring
    syl
    pmat1ovd.i
    pmat1ovd.j
    pmat1ovd.u
    mat1ov
end
