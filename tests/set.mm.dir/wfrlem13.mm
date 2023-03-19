include "cv.mm"
include "cdm.mm"
include "cdif.mm"
include "wcel.mm"
include "cpred.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wfun.mm"
include "wceq.mm"
include "wa.mm"
include "wfn.mm"
include "cin.mm"
include "c0.mm"
include "wfrfun.mm"
include "vex.mm"
include "fvex.mm"
include "funsn.mm"
include "pm3.2i.mm"
include "dmsnop.mm"
include "ineq2i.mm"
include "wn.mm"
include "eldifn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "funun.mm"
include "sylancr.mm"
include "dmun.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "jctir.mm"
include "fneq1i.mm"
include "df-fn.mm"
include "bitri.mm"

theorem wfrlem13
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume wfrlem13.1: |- R We A
  assume wfrlem13.2: |- R Se A
  assume wfrlem13.3: |- F = wrecs ( R , A , G )
  assume wfrlem13.4: |- C = ( F u. { <. z , ( G ` ( F |` Pred ( R , A , z ) ) ) >. } )

  disjoint A z
  disjoint F z
  disjoint R z
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint C f
  disjoint C x
  disjoint C y
  assert |- ( z e. ( A \ dom F ) -> C Fn ( dom F u. { z } ) )

  proof
    vz
    cv
    #
    cA
    cF
    cdm
    #
    cdif
    wcel
    #
    cF
    @0
    cF
    cA
    cR
    @0
    cpred
    cres
    #
    cG
    cfv
    #
    cop
    csn
    #
    cun
    #
    wfun
    #
    @6
    cdm
    #
    @1
    @0
    csn
    #
    cun
    #
    wceq
    #
    wa
    #
    cC
    @10
    wfn
    #
    @2
    @7
    @11
    @2
    cF
    wfun
    #
    @5
    wfun
    #
    wa
    @1
    @5
    cdm
    #
    cin
    #
    c0
    wceq
    @7
    @14
    @15
    cA
    cR
    cF
    cG
    wfrlem13.1
    wfrlem13.2
    wfrlem13.3
    wfrfun
    @0
    @4
    vz
    vex
    @3
    cG
    fvex
    #
    funsn
    pm3.2i
    @2
    @17
    @1
    @9
    cin
    #
    c0
    @16
    @9
    @1
    @0
    @4
    @18
    dmsnop
    #
    ineq2i
    @2
    @0
    @1
    wcel
    wn
    @19
    c0
    wceq
    @0
    cA
    @1
    eldifn
    @1
    @0
    disjsn
    sylibr
    syl5eq
    cF
    @5
    funun
    sylancr
    @8
    @1
    @16
    cun
    @10
    cF
    @5
    dmun
    @16
    @9
    @1
    @20
    uneq2i
    eqtri
    jctir
    @13
    @6
    @10
    wfn
    @12
    @10
    cC
    @6
    wfrlem13.4
    fneq1i
    @6
    @10
    df-fn
    bitri
    sylibr
end
