include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "con0.mm"
include "eqid.mm"
include "ply1ascl.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "subrgascl.mm"

theorem subrg1ascl
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  assume subrg1ascl.p: |- P = ( Poly1 ` R )
  assume subrg1ascl.a: |- A = ( algSc ` P )
  assume subrg1ascl.h: |- H = ( R |`s T )
  assume subrg1ascl.u: |- U = ( Poly1 ` H )
  assume subrg1ascl.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrg1ascl.c: |- C = ( algSc ` U )


  assert |- ( ph -> C = ( A |` T ) )

  proof
    wph
    cA
    cC
    c1o
    cR
    cmpl
    co
    #
    cR
    cT
    c1o
    cH
    cmpl
    co
    #
    cH
    c1o
    con0
    @0
    eqid
    cA
    cP
    cR
    subrg1ascl.p
    subrg1ascl.a
    ply1ascl
    subrg1ascl.h
    @1
    eqid
    c1o
    con0
    wcel
    wph
    1on
    a1i
    subrg1ascl.r
    cC
    cU
    cH
    subrg1ascl.u
    subrg1ascl.c
    ply1ascl
    subrgascl
end
