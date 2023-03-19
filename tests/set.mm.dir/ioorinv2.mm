include "cioo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cop.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csup.mm"
include "cif.mm"
include "crn.mm"
include "wcel.mm"
include "ioorebas.mm"
include "ioorval.mm"
include "ax-mp.mm"
include "ifnefalse.mm"
include "cv.mm"
include "wex.mm"
include "wa.mm"
include "n0.mm"
include "eliooxr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "simpld.mm"
include "simprd.mm"
include "id.mm"
include "df-ioo.mm"
include "wbr.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxlb.mm"
include "syl3anc.mm"
include "ixxub.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem ioorinv2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ioorf.1: |- F = ( x e. ran (,) |-> if ( x = (/) , <. 0 , 0 >. , <. inf ( x , RR* , < ) , sup ( x , RR* , < ) >. ) )

  disjoint A x
  disjoint B x
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F a
  disjoint F b
  assert |- ( ( A (,) B ) =/= (/) -> ( F ` ( A (,) B ) ) = <. A , B >. )

  proof
    cA
    cB
    cioo
    co
    #
    c0
    wne
    #
    @0
    cF
    cfv
    #
    @0
    c0
    wceq
    cc0
    cc0
    cop
    #
    @0
    cxr
    clt
    cinf
    #
    @0
    cxr
    clt
    csup
    #
    cop
    #
    cif
    #
    cA
    cB
    cop
    #
    @0
    cioo
    crn
    wcel
    @2
    @7
    wceq
    cA
    cB
    ioorebas
    vx
    @0
    cF
    ioorf.1
    ioorval
    ax-mp
    @1
    @7
    @6
    @8
    @0
    c0
    @3
    @6
    ifnefalse
    @1
    @4
    cA
    @5
    cB
    @1
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    @4
    cA
    wceq
    @1
    @9
    @10
    @1
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @9
    @10
    wa
    #
    vx
    @0
    n0
    @12
    @13
    vx
    @11
    cA
    cB
    eliooxr
    exlimiv
    sylbi
    #
    simpld
    #
    @1
    @9
    @10
    @14
    simprd
    #
    @1
    id
    #
    vx
    vy
    vz
    vw
    cA
    cB
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    #
    vw
    cv
    #
    cxr
    wcel
    #
    @10
    wa
    @19
    cB
    clt
    wbr
    idd
    #
    @19
    cB
    xrltle
    #
    @9
    @20
    wa
    cA
    @19
    clt
    wbr
    idd
    #
    cA
    @19
    xrltle
    #
    ixxlb
    syl3anc
    @1
    @9
    @10
    @1
    @5
    cB
    wceq
    @15
    @16
    @17
    vx
    vy
    vz
    vw
    cA
    cB
    clt
    clt
    cioo
    @18
    @21
    @22
    @23
    @24
    ixxub
    syl3anc
    opeq12d
    eqtrd
    syl5eq
end
