include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cprod.mm"
include "cmpt.mm"
include "eqid.mm"
include "etransclem29.mm"

theorem etransclem30
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vj: setvar j
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vk: setvar k
  assume etransclem30.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem30.a: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem30.p: |- ( ph -> P e. NN )
  assume etransclem30.m: |- ( ph -> M e. NN0 )
  assume etransclem30.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem30.n: |- ( ph -> N e. NN0 )
  assume etransclem30.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem30.c: |- C = ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } )

  disjoint C c
  disjoint H c
  disjoint H j
  disjoint H n
  disjoint H x
  disjoint c j
  disjoint c n
  disjoint c x
  disjoint j n
  disjoint j x
  disjoint n x
  disjoint M c
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint N c
  disjoint N j
  disjoint N n
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S c
  disjoint S j
  disjoint S n
  disjoint S x
  disjoint X j
  disjoint X n
  disjoint X x
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( S Dn F ) ` N ) = ( x e. X |-> sum_ c e. ( C ` N ) ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( c ` j ) ) ) x. prod_ j e. ( 0 ... M ) ( ( ( S Dn ( H ` j ) ) ` ( c ` j ) ) ` x ) ) ) )

  proof
    wph
    vx
    cC
    cP
    cS
    vj
    vn
    vx
    cX
    cc0
    cM
    cfz
    co
    vx
    cv
    vj
    cv
    cH
    cfv
    cfv
    vj
    cprod
    cmpt
    #
    cF
    cH
    cM
    cN
    cX
    vc
    etransclem30.s
    etransclem30.a
    etransclem30.p
    etransclem30.m
    etransclem30.f
    etransclem30.n
    etransclem30.h
    etransclem30.c
    @0
    eqid
    etransclem29
end
