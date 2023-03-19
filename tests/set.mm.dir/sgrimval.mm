include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cngp.mm"
include "wa.mm"
include "sgrim.mm"
include "oveqd.mm"
include "ad2antlr.mm"

theorem sgrimval
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  assume sgrim.x: |- X = ( T |`s U )
  assume sgrim.d: |- D = ( dist ` T )
  assume sgrim.e: |- E = ( dist ` X )
  assume sgrimval.t: |- T = ( G toNrmGrp N )
  assume sgrimval.n: |- N = ( norm ` G )
  assume sgrimval.s: |- S = ( SubGrp ` T )


  assert |- ( ( ( G e. NrmGrp /\ U e. S ) /\ ( A e. U /\ B e. U ) ) -> ( A E B ) = ( A D B ) )

  proof
    cU
    cS
    wcel
    #
    cA
    cB
    cE
    co
    cA
    cB
    cD
    co
    wceq
    cG
    cngp
    wcel
    cA
    cU
    wcel
    cB
    cU
    wcel
    wa
    @0
    cE
    cD
    cA
    cB
    cD
    cS
    cT
    cU
    cE
    cX
    sgrim.x
    sgrim.d
    sgrim.e
    sgrim
    oveqd
    ad2antlr
end
