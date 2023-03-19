include "cr.mm"
include "cv.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cc0.mm"
include "cmpt.mm"
include "cn.mm"
include "wceq.mm"
include "negeq.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "ifbieq1d.mm"
include "mpteq2dv.mm"
include "reex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem mbfi1fseqlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cJ: class J
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume mbfi1fseq.1: |- ( ph -> F e. MblFn )
  assume mbfi1fseq.2: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume mbfi1fseq.3: |- J = ( m e. NN , y e. RR |-> ( ( |_ ` ( ( F ` y ) x. ( 2 ^ m ) ) ) / ( 2 ^ m ) ) )
  assume mbfi1fseq.4: |- G = ( m e. NN |-> ( x e. RR |-> if ( x e. ( -u m [,] m ) , if ( ( m J x ) <_ m , ( m J x ) , m ) , 0 ) ) )

  disjoint m x
  disjoint m y
  disjoint F m
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint J m
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G g
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint j ph
  disjoint k ph
  disjoint n ph
  assert |- ( A e. NN -> ( G ` A ) = ( x e. RR |-> if ( x e. ( -u A [,] A ) , if ( ( A J x ) <_ A , ( A J x ) , A ) , 0 ) ) )

  proof
    vm
    cA
    vx
    cr
    vx
    cv
    #
    vm
    cv
    #
    cneg
    #
    @1
    cicc
    co
    #
    wcel
    #
    @1
    @0
    cJ
    co
    #
    @1
    cle
    wbr
    #
    @5
    @1
    cif
    #
    cc0
    cif
    #
    cmpt
    vx
    cr
    @0
    cA
    cneg
    #
    cA
    cicc
    co
    #
    wcel
    #
    cA
    @0
    cJ
    co
    #
    cA
    cle
    wbr
    #
    @12
    cA
    cif
    #
    cc0
    cif
    #
    cmpt
    cn
    cG
    @1
    cA
    wceq
    #
    vx
    cr
    @8
    @15
    @16
    @4
    @11
    @7
    @14
    cc0
    @16
    @3
    @10
    @0
    @16
    @2
    @9
    @1
    cA
    cicc
    @1
    cA
    negeq
    @16
    id
    #
    oveq12d
    eleq2d
    @16
    @6
    @13
    @5
    @1
    @12
    cA
    @16
    @5
    @12
    @1
    cA
    cle
    @1
    cA
    @0
    cJ
    oveq1
    #
    @17
    breq12d
    @18
    @17
    ifbieq12d
    ifbieq1d
    mpteq2dv
    mbfi1fseq.4
    vx
    cr
    @15
    reex
    mptex
    fvmpt
end
