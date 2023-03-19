include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "cind.mm"
include "wceq.mm"
include "df-ind.mm"
include "a1i.mm"
include "pweq.mm"
include "mpteq1.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "elex.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "fvmptd.mm"

theorem indv
  let vx: setvar x
  let cO: class O
  let cV: class V
  let va: setvar a
  let vo: setvar o

  disjoint a x
  disjoint O a
  disjoint O x
  disjoint V a
  disjoint a o
  disjoint o x
  disjoint O o
  disjoint V o
  assert |- ( O e. V -> ( _Ind ` O ) = ( a e. ~P O |-> ( x e. O |-> if ( x e. a , 1 , 0 ) ) ) )

  proof
    cO
    cV
    wcel
    #
    vo
    cO
    va
    vo
    cv
    #
    cpw
    #
    vx
    @1
    vx
    cv
    va
    cv
    wcel
    c1
    cc0
    cif
    #
    cmpt
    #
    cmpt
    #
    va
    cO
    cpw
    #
    vx
    cO
    @3
    cmpt
    #
    cmpt
    #
    cvv
    cind
    cvv
    cind
    vo
    cvv
    @5
    cmpt
    wceq
    @0
    vx
    vo
    va
    df-ind
    a1i
    @1
    cO
    wceq
    #
    @5
    @8
    wceq
    @0
    @9
    va
    @2
    @4
    @6
    @7
    @1
    cO
    pweq
    vx
    @1
    cO
    @3
    mpteq1
    mpteq12dv
    adantl
    cO
    cV
    elex
    #
    @0
    cO
    cvv
    wcel
    @6
    cvv
    wcel
    @8
    cvv
    wcel
    @10
    cO
    cvv
    pwexg
    va
    @6
    @7
    cvv
    mptexg
    3syl
    fvmptd
end
