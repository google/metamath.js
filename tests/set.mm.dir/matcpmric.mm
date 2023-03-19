include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cric.mm"
include "wbr.mm"
include "cmat2pmat.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "m2cpmrngiso.mm"
include "ne0i.mm"
include "syl.mm"
include "brric.mm"
include "sylibr.mm"

theorem matcpmric
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cN: class N
  assume matcpmric.a: |- A = ( N Mat R )
  assume matcpmric.p: |- P = ( Poly1 ` R )
  assume matcpmric.c: |- C = ( N Mat P )
  assume matcpmric.s: |- S = ( N ConstPolyMat R )
  assume matcpmric.u: |- U = ( C |`s S )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> A ~=r U )

  proof
    cN
    cfn
    wcel
    cR
    ccrg
    wcel
    wa
    #
    cA
    cU
    crs
    co
    #
    c0
    wne
    #
    cA
    cU
    cric
    wbr
    @0
    cN
    cR
    cmat2pmat
    co
    #
    @1
    wcel
    @2
    cA
    cC
    cP
    cR
    cS
    @3
    cU
    cA
    cbs
    cfv
    #
    cN
    matcpmric.s
    @3
    eqid
    matcpmric.a
    @4
    eqid
    matcpmric.p
    matcpmric.c
    matcpmric.u
    m2cpmrngiso
    @1
    @3
    ne0i
    syl
    cA
    cU
    brric
    sylibr
end
