include "cv.mm"
include "wel.mm"
include "weq.mm"
include "cif.mm"
include "cop.mm"
include "cun.mm"
include "elequ1.mm"
include "opeq1.mm"
include "equequ1.mm"
include "ifbid.mm"
include "opeq2d.mm"
include "eqtrd.mm"
include "opeq1d.mm"
include "opeq2.mm"
include "ifbieq12d.mm"
include "syl5eq.mm"
include "opex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem unxpdomlem1
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  assume unxpdomlem1.1: |- F = ( x e. ( a u. b ) |-> G )
  assume unxpdomlem1.2: |- G = if ( x e. a , <. x , if ( x = m , t , s ) >. , <. if ( x = t , n , m ) , x >. )

  disjoint F z
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint b z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint m z
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint s t
  disjoint s x
  disjoint s z
  disjoint t x
  disjoint t z
  disjoint x z
  disjoint F w
  disjoint w z
  disjoint a w
  disjoint b w
  disjoint m w
  disjoint n w
  disjoint s w
  disjoint t w
  disjoint w x
  assert |- ( z e. ( a u. b ) -> ( F ` z ) = if ( z e. a , <. z , if ( z = m , t , s ) >. , <. if ( z = t , n , m ) , z >. ) )

  proof
    vx
    vz
    cv
    #
    cG
    vz
    va
    wel
    #
    @0
    vz
    vm
    weq
    #
    vt
    cv
    #
    vs
    cv
    #
    cif
    #
    cop
    #
    vz
    vt
    weq
    #
    vn
    cv
    #
    vm
    cv
    #
    cif
    #
    @0
    cop
    #
    cif
    #
    va
    cv
    vb
    cv
    cun
    cF
    vx
    vz
    weq
    #
    cG
    vx
    va
    wel
    #
    vx
    cv
    #
    vx
    vm
    weq
    #
    @3
    @4
    cif
    #
    cop
    #
    vx
    vt
    weq
    #
    @8
    @9
    cif
    #
    @15
    cop
    #
    cif
    @12
    unxpdomlem1.2
    @13
    @14
    @1
    @18
    @21
    @6
    @11
    vx
    vz
    va
    elequ1
    @13
    @18
    @0
    @17
    cop
    @6
    @15
    @0
    @17
    opeq1
    @13
    @17
    @5
    @0
    @13
    @16
    @2
    @3
    @4
    vx
    vz
    vm
    equequ1
    ifbid
    opeq2d
    eqtrd
    @13
    @21
    @10
    @15
    cop
    @11
    @13
    @20
    @10
    @15
    @13
    @19
    @7
    @8
    @9
    vx
    vz
    vt
    equequ1
    ifbid
    opeq1d
    @15
    @0
    @10
    opeq2
    eqtrd
    ifbieq12d
    syl5eq
    unxpdomlem1.1
    @1
    @6
    @11
    @0
    @5
    opex
    @10
    @0
    opex
    ifex
    fvmpt
end
